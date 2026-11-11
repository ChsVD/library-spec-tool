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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import get_naf_w3_def.
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

(*----- Function get_naf_w3 -----*)

Definition get_naf_w3_safety_wit_1_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.undef_full naf_w3_pre 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_2_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) K_non_alias )
  **  (UInt64Array.full &(( &( "x" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  (CharArray.undef_full naf_w3_pre 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_3_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 257)) (PreH3 : (i = (Zlength (digits)))) (PreH4 : (0 <= Kcur)) (PreH5 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH6 : ((i >= 257) -> (Kcur = 0))) (PreH7 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH8 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH9 : (wnaf3_separated digits )) (PreH10 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH11 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH12 : (0 <= X)) (PreH13 : (X < U64_MOD)) ,
  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (257 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 257) ”
.

Definition get_naf_w3_safety_wit_4_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (i < 257)) (PreH20 : (0 <= i)) (PreH21 : (i <= 257)) (PreH22 : (i = (Zlength (digits)))) (PreH23 : (0 <= Kcur)) (PreH24 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH25 : ((i >= 257) -> (Kcur = 0))) (PreH26 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH28 : (wnaf3_separated digits )) (PreH29 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH30 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH31 : (0 <= X)) (PreH32 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_5_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (i < 257)) (PreH20 : (0 <= i)) (PreH21 : (i <= 257)) (PreH22 : (i = (Zlength (digits)))) (PreH23 : (0 <= Kcur)) (PreH24 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH25 : ((i >= 257) -> (Kcur = 0))) (PreH26 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH28 : (wnaf3_separated digits )) (PreH29 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH30 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH31 : (0 <= X)) (PreH32 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition get_naf_w3_safety_wit_6_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (i < 257)) (PreH20 : (0 <= i)) (PreH21 : (i <= 257)) (PreH22 : (i = (Zlength (digits)))) (PreH23 : (0 <= Kcur)) (PreH24 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH25 : ((i >= 257) -> (Kcur = 0))) (PreH26 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH28 : (wnaf3_separated digits )) (PreH29 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH30 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH31 : (0 <= X)) (PreH32 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_naf_w3_safety_wit_7_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (i < 257)) (PreH20 : (0 <= i)) (PreH21 : (i <= 257)) (PreH22 : (i = (Zlength (digits)))) (PreH23 : (0 <= Kcur)) (PreH24 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH25 : ((i >= 257) -> (Kcur = 0))) (PreH26 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH27 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH28 : (wnaf3_separated digits )) (PreH29 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH30 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH31 : (0 <= X)) (PreH32 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_8_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH2 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits)))) (PreH24 : (0 <= Kcur)) (PreH25 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH29 : (wnaf3_separated digits )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH32 : (0 <= X)) (PreH33 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition get_naf_w3_safety_wit_9_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) (PreH12 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0_2 < U64_MOD)) (PreH20 : (0 <= x0_2)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 ) <= 127) ” 
  &&  “ ((-128) <= ((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) (PreH12 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0_2 < U64_MOD)) (PreH20 : (0 <= x0_2)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 ) <= 127) ” 
  &&  “ ((-128) <= ((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) ”
).

Definition get_naf_w3_safety_wit_9_non_alias_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) (PreH12 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0_2 < U64_MOD)) (PreH20 : (0 <= x0_2)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 ) <= 127) ”
.

Definition get_naf_w3_safety_wit_9_non_alias_split_goal_2 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0 < U64_MOD)) (PreH11 : (0 <= x0)) (PreH12 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0_2 < U64_MOD)) (PreH20 : (0 <= x0_2)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((-128) <= ((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) ”
.

Definition get_naf_w3_safety_wit_10_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition get_naf_w3_safety_wit_11_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_12_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH2 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH3 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH4 : (x3_2 < U64_MOD)) (PreH5 : (0 <= x3_2)) (PreH6 : (x2_2 < U64_MOD)) (PreH7 : (0 <= x2_2)) (PreH8 : (x1_2 < U64_MOD)) (PreH9 : (0 <= x1_2)) (PreH10 : (x0_2 < U64_MOD)) (PreH11 : (0 <= x0_2)) (PreH12 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH13 : (x3 < U64_MOD)) (PreH14 : (0 <= x3)) (PreH15 : (x2 < U64_MOD)) (PreH16 : (0 <= x2)) (PreH17 : (x1 < U64_MOD)) (PreH18 : (0 <= x1)) (PreH19 : (x0 < U64_MOD)) (PreH20 : (0 <= x0)) (PreH21 : (i < 257)) (PreH22 : (0 <= i)) (PreH23 : (i <= 257)) (PreH24 : (i = (Zlength (digits)))) (PreH25 : (0 <= Kcur)) (PreH26 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH27 : ((i >= 257) -> (Kcur = 0))) (PreH28 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH29 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH30 : (wnaf3_separated digits )) (PreH31 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH32 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH33 : (0 <= X)) (PreH34 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_13_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_14_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_15_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_16_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_17_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) <> (INT_MIN)) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) <> (INT_MIN)) ”
).

Definition get_naf_w3_safety_wit_17_non_alias_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) <> (INT_MIN)) ”
.

Definition get_naf_w3_safety_wit_18_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0) (8)) 7) <> (INT_MIN)) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0) (8)) 7) <> (INT_MIN)) ”
).

Definition get_naf_w3_safety_wit_18_non_alias_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0) (8)) 7) <> (INT_MIN)) ”
.

Definition get_naf_w3_safety_wit_19_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits)))) (PreH24 : (0 <= Kcur)) (PreH25 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH29 : (wnaf3_separated digits )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH32 : (0 <= X)) (PreH33 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_naf_w3_safety_wit_20_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_naf_w3_safety_wit_21_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) )
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_naf_w3_safety_wit_22_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_naf_w3_safety_wit_23_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_naf_w3_safety_wit_24_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits)))) (PreH24 : (0 <= Kcur)) (PreH25 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH29 : (wnaf3_separated digits )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH32 : (0 <= X)) (PreH33 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_naf_w3_entail_wit_1_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) K_non_alias )
  **  (UInt64Array.full &(( &( "x" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (CharArray.undef_full naf_w3_pre 257 )
|--
  EX (X: Z)  (Kcur: Z)  (digits: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 257) ” 
  &&  “ (0 = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((0 <= 256) -> (Kcur <= (Z.pow (2) ((256 - 0 ))))) ” 
  &&  “ ((0 >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (0)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((0 >= 1) /\ ((Znth ((0 - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((0 >= 2) /\ ((Znth ((0 - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  (CharArray.full naf_w3_pre 0 digits )
  **  (CharArray.undef_seg naf_w3_pre 0 257 )
) \/
(
forall (K_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  TT && emp 
|--
  “ ((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) < U64_MOD) ” 
  &&  “ (0 <= (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) )))) ” 
  &&  “ (wnaf3_separated (@nil Z) ) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> (wnaf3_digit (Znth (j) ((@nil Z)) (0)) )) ” 
  &&  “ (K_non_alias = ((wnaf3_value ((@nil Z))) + (K_non_alias * (Z.pow (2) (0)) ) )) ” 
  &&  “ ((0 <= 256) -> (K_non_alias <= (Z.pow (2) ((256 - 0 ))))) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  emp
).

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_1 := 
forall (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  ((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) < U64_MOD)
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_2 := 
forall (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (0 <= (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))))
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_3 := 
forall (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (wnaf3_separated (@nil Z) )
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_4 := 
forall (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  forall (j: Z) , (((0 <= j) /\ (j < 0)) -> (wnaf3_digit (Znth (j) ((@nil Z)) (0)) ))
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_5 := 
forall (K_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (K_non_alias = ((wnaf3_value ((@nil Z))) + (K_non_alias * (Z.pow (2) (0)) ) ))
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_6 := 
forall (K_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  ((0 <= 256) -> (K_non_alias <= (Z.pow (2) ((256 - 0 )))))
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_7 := 
forall (K_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (0 <= K_non_alias)
.

Definition get_naf_w3_entail_wit_1_non_alias_split_goal_8 := 
forall (retval: Z) (PreH1 : (retval = ( &( "k" ) ))) ,
  (0 = (Zlength ((@nil Z))))
.

Definition get_naf_w3_entail_wit_2_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (PreH1 : (i < 257)) (PreH2 : (0 <= i)) (PreH3 : (i <= 257)) (PreH4 : (i = (Zlength (digits)))) (PreH5 : (0 <= Kcur)) (PreH6 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH7 : ((i >= 257) -> (Kcur = 0))) (PreH8 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH10 : (wnaf3_separated digits )) (PreH11 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH12 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH13 : (0 <= X)) (PreH14 : (X < U64_MOD)) ,
  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_entail_wit_3_1_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_entail_wit_3_2_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_entail_wit_4_1_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_entail_wit_4_2_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0_2 < U64_MOD)) (PreH12 : (0 <= x0_2)) (PreH13 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0 < U64_MOD)) (PreH21 : (0 <= x0)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_entail_wit_5_1_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
|--
  EX (X: Z)  (Kcur: Z)  (digits: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 257) ” 
  &&  “ ((i + 1 ) = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ (((i + 1 ) <= 256) -> (Kcur <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (((i + 1 ) >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre (i + 1 ) digits )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
) \/
(
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  TT && emp 
|--
  “ ((u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) < U64_MOD) ” 
  &&  “ (0 <= (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3))) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0)) ” 
  &&  “ (wnaf3_separated (app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) ) ” 
  &&  “ (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0)) ” 
  &&  “ (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (0 <= (S ÷ 2 )) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))))) ”
  &&  emp
).

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) < U64_MOD)
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_4 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_5 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (wnaf3_separated (app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_6 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) ))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_7 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_8 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) )))))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_9 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (S ÷ 2 ))
.

Definition get_naf_w3_entail_wit_5_1_non_alias_split_goal_10 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))))))
.

Definition get_naf_w3_entail_wit_5_2_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
|--
  EX (X: Z)  (Kcur: Z)  (digits: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 257) ” 
  &&  “ ((i + 1 ) = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ (((i + 1 ) <= 256) -> (Kcur <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (((i + 1 ) >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre (i + 1 ) digits )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
) \/
(
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  TT && emp 
|--
  “ ((u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) < U64_MOD) ” 
  &&  “ (0 <= (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3))) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0)) ” 
  &&  “ (wnaf3_separated (app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) ) ” 
  &&  “ (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0)) ” 
  &&  “ (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (0 <= (S ÷ 2 )) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))))) ”
  &&  emp
).

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) < U64_MOD)
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_4 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_5 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (wnaf3_separated (app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_6 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) ))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_7 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_8 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) )))))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_9 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (S ÷ 2 ))
.

Definition get_naf_w3_entail_wit_5_2_non_alias_split_goal_10 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))))))
.

Definition get_naf_w3_entail_wit_5_3_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))
|--
  EX (X: Z)  (Kcur: Z)  (digits: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 257) ” 
  &&  “ ((i + 1 ) = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ (((i + 1 ) <= 256) -> (Kcur <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (((i + 1 ) >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre (i + 1 ) digits )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
) \/
(
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  TT && emp 
|--
  “ ((u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) < U64_MOD) ” 
  &&  “ (0 <= (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3))) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0)) ” 
  &&  “ (wnaf3_separated (app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) ) ” 
  &&  “ (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0)) ” 
  &&  “ (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (0 <= (S ÷ 2 )) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))))) ”
  &&  emp
).

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) < U64_MOD)
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_4 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_5 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (wnaf3_separated (app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_6 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) ))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_7 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_8 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) )))))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_9 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (S ÷ 2 ))
.

Definition get_naf_w3_entail_wit_5_3_non_alias_split_goal_10 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))))))
.

Definition get_naf_w3_entail_wit_5_4_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) (S ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
|--
  EX (X: Z)  (Kcur: Z)  (digits: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 257) ” 
  &&  “ ((i + 1 ) = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ (((i + 1 ) <= 256) -> (Kcur <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (((i + 1 ) >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre (i + 1 ) digits )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
) \/
(
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  TT && emp 
|--
  “ ((u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) < U64_MOD) ” 
  &&  “ (0 <= (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3))) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0)) ” 
  &&  “ (wnaf3_separated (app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) ) ” 
  &&  “ (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0)) ” 
  &&  “ (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (0 <= (S ÷ 2 )) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))))) ”
  &&  emp
).

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) < U64_MOD)
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 2 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_4 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z)))))) (0)) <> 0)) -> (((S ÷ 2 ) % ( 4 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_5 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (wnaf3_separated (app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_6 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))))) + ((S ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) ))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_7 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) >= 257) -> ((S ÷ 2 ) = 0))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_8 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (((i + 1 ) <= 256) -> ((S ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) )))))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_9 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  (0 <= (S ÷ 2 ))
.

Definition get_naf_w3_entail_wit_5_4_non_alias_split_goal_10 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits_2)))) (PreH31 : (0 <= Kcur_2)) (PreH32 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur_2 = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH36 : (wnaf3_separated digits_2 )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH39 : (0 <= X_2)) (PreH40 : (X_2 < U64_MOD)) ,
  ((i + 1 ) = (Zlength ((app (digits_2) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))))))
.

Definition get_naf_w3_entail_wit_5_5_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) ÷ 2 ) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0_2) (8)) 7))
|--
  EX (X: Z)  (Kcur: Z)  (digits: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 257) ” 
  &&  “ ((i + 1 ) = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ (((i + 1 ) <= 256) -> (Kcur <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (((i + 1 ) >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (store_u256 ( &( "k" ) ) Kcur )
  **  (store_u256 ( &( "x" ) ) X )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  (CharArray.full naf_w3_pre (i + 1 ) digits )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
) \/
(
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  TT && emp 
|--
  “ ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons (0) ((@nil Z)))))) (0)) <> 0)) -> (((Kcur_2 ÷ 2 ) % ( 2 ) ) = 0)) ” 
  &&  “ ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons (0) ((@nil Z)))))) (0)) <> 0)) -> (((Kcur_2 ÷ 2 ) % ( 4 ) ) = 0)) ” 
  &&  “ (wnaf3_separated (app (digits_2) ((cons (0) ((@nil Z))))) ) ” 
  &&  “ (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons (0) ((@nil Z))))))) + ((Kcur_2 ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) )) ” 
  &&  “ (((i + 1 ) >= 257) -> ((Kcur_2 ÷ 2 ) = 0)) ” 
  &&  “ (((i + 1 ) <= 256) -> ((Kcur_2 ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) ))))) ” 
  &&  “ (0 <= (Kcur_2 ÷ 2 )) ” 
  &&  “ ((i + 1 ) = (Zlength ((app (digits_2) ((cons (0) ((@nil Z)))))))) ”
  &&  emp
).

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 2) /\ ((Znth (((i + 1 ) - 2 )) ((app (digits_2) ((cons (0) ((@nil Z)))))) (0)) <> 0)) -> (((Kcur_2 ÷ 2 ) % ( 2 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  ((((i + 1 ) >= 1) /\ ((Znth (((i + 1 ) - 1 )) ((app (digits_2) ((cons (0) ((@nil Z)))))) (0)) <> 0)) -> (((Kcur_2 ÷ 2 ) % ( 4 ) ) = 0))
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  (wnaf3_separated (app (digits_2) ((cons (0) ((@nil Z))))) )
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_4 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  (K_non_alias = ((wnaf3_value ((app (digits_2) ((cons (0) ((@nil Z))))))) + ((Kcur_2 ÷ 2 ) * (Z.pow (2) ((i + 1 ))) ) ))
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_5 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  (((i + 1 ) >= 257) -> ((Kcur_2 ÷ 2 ) = 0))
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_6 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  (((i + 1 ) <= 256) -> ((Kcur_2 ÷ 2 ) <= (Z.pow (2) ((256 - (i + 1 ) )))))
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_7 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  (0 <= (Kcur_2 ÷ 2 ))
.

Definition get_naf_w3_entail_wit_5_5_non_alias_split_goal_8 := 
forall (K_non_alias: Z) (X_2: Z) (Kcur_2: Z) (digits_2: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur_2 = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X_2 = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits_2)))) (PreH24 : (0 <= Kcur_2)) (PreH25 : ((i <= 256) -> (Kcur_2 <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur_2 = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits_2)) + (Kcur_2 * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits_2) (0)) ))) (PreH29 : (wnaf3_separated digits_2 )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits_2) (0)) <> 0)) -> ((Kcur_2 % ( 2 ) ) = 0))) (PreH32 : (0 <= X_2)) (PreH33 : (X_2 < U64_MOD)) ,
  ((i + 1 ) = (Zlength ((app (digits_2) ((cons (0) ((@nil Z))))))))
.

Definition get_naf_w3_return_wit_1_non_alias := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (PreH1 : (i >= 257)) (PreH2 : (0 <= i)) (PreH3 : (i <= 257)) (PreH4 : (i = (Zlength (digits)))) (PreH5 : (0 <= Kcur)) (PreH6 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH7 : ((i >= 257) -> (Kcur = 0))) (PreH8 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH10 : (wnaf3_separated digits )) (PreH11 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH12 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH13 : (0 <= X)) (PreH14 : (X < U64_MOD)) ,
  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
|--
  (store_fn pk_pre K_non_alias )
  **  (store_wnaf3 naf_w3_pre K_non_alias )
) \/
(
forall (naf_w3_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (PreH1 : (i >= 257)) (PreH2 : (0 <= i)) (PreH3 : (i <= 257)) (PreH4 : (i = (Zlength (digits)))) (PreH5 : (0 <= Kcur)) (PreH6 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH7 : ((i >= 257) -> (Kcur = 0))) (PreH8 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH10 : (wnaf3_separated digits )) (PreH11 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH12 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH13 : (0 <= X)) (PreH14 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre i digits )
|--
  (store_wnaf3 naf_w3_pre K_non_alias )
).

Definition get_naf_w3_return_wit_1_non_alias_split_goal_spatial := 
forall (naf_w3_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (PreH1 : (i >= 257)) (PreH2 : (0 <= i)) (PreH3 : (i <= 257)) (PreH4 : (i = (Zlength (digits)))) (PreH5 : (0 <= Kcur)) (PreH6 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH7 : ((i >= 257) -> (Kcur = 0))) (PreH8 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH9 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH10 : (wnaf3_separated digits )) (PreH11 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH12 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH13 : (0 <= X)) (PreH14 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre i digits )
|--
  (store_wnaf3 naf_w3_pre K_non_alias )
.

Definition get_naf_w3_partial_solve_wit_1_non_alias_pure := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) ,
  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "x" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.undef_full naf_w3_pre 257 )
|--
  “ (sizeof( "u32" ) = 32) ”
.

Definition get_naf_w3_partial_solve_wit_1_non_alias_aux := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) ,
  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "x" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.undef_full naf_w3_pre 257 )
|--
  “ (sizeof( "u32" ) = 32) ”
  &&  (store_fn pk_pre K_non_alias )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "x" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (CharArray.undef_full naf_w3_pre 257 )
.

Definition get_naf_w3_partial_solve_wit_1_non_alias := get_naf_w3_partial_solve_wit_1_non_alias_pure -> get_naf_w3_partial_solve_wit_1_non_alias_aux.

Definition get_naf_w3_partial_solve_wit_2_non_alias_pure := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) < U64_MOD) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (i <= INT_MAX)) (PreH18 : (i >= INT_MIN)) (PreH19 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) >= 0)) (PreH20 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH21 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH22 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (i < 257)) (PreH41 : (0 <= i)) (PreH42 : (i <= 257)) (PreH43 : (i = (Zlength (digits)))) (PreH44 : (0 <= Kcur)) (PreH45 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH46 : ((i >= 257) -> (Kcur = 0))) (PreH47 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH48 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH49 : (wnaf3_separated digits )) (PreH50 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH51 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH52 : (0 <= X)) (PreH53 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) < U64_MOD) ”
).

Definition get_naf_w3_partial_solve_wit_2_non_alias_pure_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (i <= INT_MAX)) (PreH18 : (i >= INT_MIN)) (PreH19 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) >= 0)) (PreH20 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH21 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH22 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (i < 257)) (PreH41 : (0 <= i)) (PreH42 : (i <= 257)) (PreH43 : (i = (Zlength (digits)))) (PreH44 : (0 <= Kcur)) (PreH45 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH46 : ((i >= 257) -> (Kcur = 0))) (PreH47 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH48 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH49 : (wnaf3_separated digits )) (PreH50 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH51 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH52 : (0 <= X)) (PreH53 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) < U64_MOD) ”
.

Definition get_naf_w3_partial_solve_wit_2_non_alias_aux := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)))
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64)) < U64_MOD) ” 
  &&  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X = (u256_of_limbs (x0_2) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_partial_solve_wit_2_non_alias := get_naf_w3_partial_solve_wit_2_non_alias_pure -> get_naf_w3_partial_solve_wit_2_non_alias_aux.

Definition get_naf_w3_partial_solve_wit_3_non_alias_pure := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < U64_MOD) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (i <= INT_MAX)) (PreH17 : (i >= INT_MIN)) (PreH18 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 0)) (PreH19 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH20 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH21 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (i < 257)) (PreH40 : (0 <= i)) (PreH41 : (i <= 257)) (PreH42 : (i = (Zlength (digits)))) (PreH43 : (0 <= Kcur)) (PreH44 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH45 : ((i >= 257) -> (Kcur = 0))) (PreH46 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH47 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH48 : (wnaf3_separated digits )) (PreH49 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH50 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH51 : (0 <= X)) (PreH52 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < U64_MOD) ”
).

Definition get_naf_w3_partial_solve_wit_3_non_alias_pure_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : (x1 >= 0)) (PreH10 : (x2 >= 0)) (PreH11 : (x3 >= 0)) (PreH12 : (x0 >= 0)) (PreH13 : (x1_2 >= 0)) (PreH14 : (x2_2 >= 0)) (PreH15 : (x3_2 >= 0)) (PreH16 : (i <= INT_MAX)) (PreH17 : (i >= INT_MIN)) (PreH18 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 0)) (PreH19 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH20 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH21 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0 < U64_MOD)) (PreH29 : (0 <= x0)) (PreH30 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (i < 257)) (PreH40 : (0 <= i)) (PreH41 : (i <= 257)) (PreH42 : (i = (Zlength (digits)))) (PreH43 : (0 <= Kcur)) (PreH44 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH45 : ((i >= 257) -> (Kcur = 0))) (PreH46 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH47 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH48 : (wnaf3_separated digits )) (PreH49 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH50 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH51 : (0 <= X)) (PreH52 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < U64_MOD) ”
.

Definition get_naf_w3_partial_solve_wit_3_non_alias_aux := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < U64_MOD) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X = (u256_of_limbs (x0_2) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0) (8)) 7)) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_partial_solve_wit_3_non_alias := get_naf_w3_partial_solve_wit_3_non_alias_pure -> get_naf_w3_partial_solve_wit_3_non_alias_aux.

Definition get_naf_w3_partial_solve_wit_4_non_alias_pure := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) < U64_MOD) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (i <= INT_MAX)) (PreH18 : (i >= INT_MIN)) (PreH19 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH20 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH21 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH22 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (i < 257)) (PreH41 : (0 <= i)) (PreH42 : (i <= 257)) (PreH43 : (i = (Zlength (digits)))) (PreH44 : (0 <= Kcur)) (PreH45 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH46 : ((i >= 257) -> (Kcur = 0))) (PreH47 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH48 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH49 : (wnaf3_separated digits )) (PreH50 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH51 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH52 : (0 <= X)) (PreH53 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) < U64_MOD) ”
).

Definition get_naf_w3_partial_solve_wit_4_non_alias_pure_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (i <= INT_MAX)) (PreH18 : (i >= INT_MIN)) (PreH19 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH20 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH21 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH22 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (i < 257)) (PreH41 : (0 <= i)) (PreH42 : (i <= 257)) (PreH43 : (i = (Zlength (digits)))) (PreH44 : (0 <= Kcur)) (PreH45 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH46 : ((i >= 257) -> (Kcur = 0))) (PreH47 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH48 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH49 : (wnaf3_separated digits )) (PreH50 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH51 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH52 : (0 <= X)) (PreH53 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) < U64_MOD) ”
.

Definition get_naf_w3_partial_solve_wit_4_non_alias_aux := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)))
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64)) < U64_MOD) ” 
  &&  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X = (u256_of_limbs (x0_2) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_partial_solve_wit_4_non_alias := get_naf_w3_partial_solve_wit_4_non_alias_pure -> get_naf_w3_partial_solve_wit_4_non_alias_aux.

Definition get_naf_w3_partial_solve_wit_5_non_alias_pure := 
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) < U64_MOD) ”
) \/
(
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (i <= INT_MAX)) (PreH18 : (i >= INT_MIN)) (PreH19 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH20 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH21 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH22 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (i < 257)) (PreH41 : (0 <= i)) (PreH42 : (i <= 257)) (PreH43 : (i = (Zlength (digits)))) (PreH44 : (0 <= Kcur)) (PreH45 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH46 : ((i >= 257) -> (Kcur = 0))) (PreH47 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH48 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH49 : (wnaf3_separated digits )) (PreH50 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH51 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH52 : (0 <= X)) (PreH53 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) < U64_MOD) ”
).

Definition get_naf_w3_partial_solve_wit_5_non_alias_pure_split_goal_1 := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) <= UINT64_MAX)) (PreH2 : (x1 <= UINT64_MAX)) (PreH3 : (x2 <= UINT64_MAX)) (PreH4 : (x3 <= UINT64_MAX)) (PreH5 : (x0 <= UINT64_MAX)) (PreH6 : (x1_2 <= UINT64_MAX)) (PreH7 : (x2_2 <= UINT64_MAX)) (PreH8 : (x3_2 <= UINT64_MAX)) (PreH9 : ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) >= 0)) (PreH10 : (x1 >= 0)) (PreH11 : (x2 >= 0)) (PreH12 : (x3 >= 0)) (PreH13 : (x0 >= 0)) (PreH14 : (x1_2 >= 0)) (PreH15 : (x2_2 >= 0)) (PreH16 : (x3_2 >= 0)) (PreH17 : (i <= INT_MAX)) (PreH18 : (i >= INT_MIN)) (PreH19 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH20 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH21 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH22 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0 < U64_MOD)) (PreH30 : (0 <= x0)) (PreH31 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (i < 257)) (PreH41 : (0 <= i)) (PreH42 : (i <= 257)) (PreH43 : (i = (Zlength (digits)))) (PreH44 : (0 <= Kcur)) (PreH45 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH46 : ((i >= 257) -> (Kcur = 0))) (PreH47 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH48 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH49 : (wnaf3_separated digits )) (PreH50 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH51 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH52 : (0 <= X)) (PreH53 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)))
  **  ((( &( "pk" ) )) # Ptr  |-> pk_pre)
  **  ((( &( "naf_w3" ) )) # Ptr  |-> naf_w3_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_fn pk_pre K_non_alias )
  **  ((( &( "ki" ) )) # Char  |-> (Z.land (signed_last_nbits (x0) (8)) 7))
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) < U64_MOD) ”
.

Definition get_naf_w3_partial_solve_wit_5_non_alias_aux := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0_2: Z) (x1: Z) (x2: Z) (x3: Z) (x0: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 0)) (PreH2 : ((Z.land (signed_last_nbits (x0) (8)) 7) < 4)) (PreH3 : ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0)) (PreH4 : (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)))) (PreH5 : (x3_2 < U64_MOD)) (PreH6 : (0 <= x3_2)) (PreH7 : (x2_2 < U64_MOD)) (PreH8 : (0 <= x2_2)) (PreH9 : (x1_2 < U64_MOD)) (PreH10 : (0 <= x1_2)) (PreH11 : (x0 < U64_MOD)) (PreH12 : (0 <= x0)) (PreH13 : (X = (u256_of_limbs (x0_2) (x1) (x2) (x3)))) (PreH14 : (x3 < U64_MOD)) (PreH15 : (0 <= x3)) (PreH16 : (x2 < U64_MOD)) (PreH17 : (0 <= x2)) (PreH18 : (x1 < U64_MOD)) (PreH19 : (0 <= x1)) (PreH20 : (x0_2 < U64_MOD)) (PreH21 : (0 <= x0_2)) (PreH22 : (i < 257)) (PreH23 : (0 <= i)) (PreH24 : (i <= 257)) (PreH25 : (i = (Zlength (digits)))) (PreH26 : (0 <= Kcur)) (PreH27 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH28 : ((i >= 257) -> (Kcur = 0))) (PreH29 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH31 : (wnaf3_separated digits )) (PreH32 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH33 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH34 : (0 <= X)) (PreH35 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> (unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)))
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (( &( "k" ) ) = ( &( "k" ) )) ” 
  &&  “ (0 <= (unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64))) ” 
  &&  “ ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64)) < U64_MOD) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X = (u256_of_limbs (x0_2) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) (u256_of_limbs (x0) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
.

Definition get_naf_w3_partial_solve_wit_5_non_alias := get_naf_w3_partial_solve_wit_5_non_alias_pure -> get_naf_w3_partial_solve_wit_5_non_alias_aux.

Definition get_naf_w3_partial_solve_wit_6_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "k" ) ) = ( &( "k" ) ))) (PreH7 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH8 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH9 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH10 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (i < 257)) (PreH29 : (0 <= i)) (PreH30 : (i <= 257)) (PreH31 : (i = (Zlength (digits)))) (PreH32 : (0 <= Kcur)) (PreH33 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH34 : ((i >= 257) -> (Kcur = 0))) (PreH35 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH36 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH37 : (wnaf3_separated digits )) (PreH38 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH39 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH40 : (0 <= X)) (PreH41 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((naf_w3_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
.

Definition get_naf_w3_partial_solve_wit_7_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "k" ) ) = ( &( "k" ) ))) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH8 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH9 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH10 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (i < 257)) (PreH29 : (0 <= i)) (PreH30 : (i <= 257)) (PreH31 : (i = (Zlength (digits)))) (PreH32 : (0 <= Kcur)) (PreH33 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH34 : ((i >= 257) -> (Kcur = 0))) (PreH35 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH36 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH37 : (wnaf3_separated digits )) (PreH38 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH39 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH40 : (0 <= X)) (PreH41 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((naf_w3_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
.

Definition get_naf_w3_partial_solve_wit_8_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : (( &( "k" ) ) = ( &( "k" ) ))) (PreH7 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH8 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH9 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH10 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (i < 257)) (PreH29 : (0 <= i)) (PreH30 : (i <= 257)) (PreH31 : (i = (Zlength (digits)))) (PreH32 : (0 <= Kcur)) (PreH33 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH34 : ((i >= 257) -> (Kcur = 0))) (PreH35 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH36 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH37 : (wnaf3_separated digits )) (PreH38 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH39 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH40 : (0 <= X)) (PreH41 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) )) ” 
  &&  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((naf_w3_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
.

Definition get_naf_w3_partial_solve_wit_9_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : (( &( "k" ) ) = ( &( "k" ) ))) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH8 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH9 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH10 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH11 : (x3_2 < U64_MOD)) (PreH12 : (0 <= x3_2)) (PreH13 : (x2_2 < U64_MOD)) (PreH14 : (0 <= x2_2)) (PreH15 : (x1_2 < U64_MOD)) (PreH16 : (0 <= x1_2)) (PreH17 : (x0_2 < U64_MOD)) (PreH18 : (0 <= x0_2)) (PreH19 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH20 : (x3 < U64_MOD)) (PreH21 : (0 <= x3)) (PreH22 : (x2 < U64_MOD)) (PreH23 : (0 <= x2)) (PreH24 : (x1 < U64_MOD)) (PreH25 : (0 <= x1)) (PreH26 : (x0 < U64_MOD)) (PreH27 : (0 <= x0)) (PreH28 : (i < 257)) (PreH29 : (0 <= i)) (PreH30 : (i <= 257)) (PreH31 : (i = (Zlength (digits)))) (PreH32 : (0 <= Kcur)) (PreH33 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH34 : ((i >= 257) -> (Kcur = 0))) (PreH35 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH36 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH37 : (wnaf3_separated digits )) (PreH38 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH39 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH40 : (0 <= X)) (PreH41 : (X < U64_MOD)) ,
  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) )) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((naf_w3_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
.

Definition get_naf_w3_partial_solve_wit_10_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits)))) (PreH24 : (0 <= Kcur)) (PreH25 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH29 : (wnaf3_separated digits )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH32 : (0 <= X)) (PreH33 : (X < U64_MOD)) ,
  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
  **  (CharArray.undef_seg naf_w3_pre i 257 )
|--
  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (((naf_w3_pre + (i * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fn pk_pre K_non_alias )
  **  (CharArray.full naf_w3_pre i digits )
.

Definition get_naf_w3_partial_solve_wit_11_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) S )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
.

Definition get_naf_w3_partial_solve_wit_12_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) - (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) S )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((Z.land (signed_last_nbits (x0_2) (8)) 7)) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
.

Definition get_naf_w3_partial_solve_wit_13_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) )) ” 
  &&  “ ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) >= 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) S )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(signed_last_nbits (((Z.land (signed_last_nbits (x0_2) (8)) 7) - 8 )) (8)))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
.

Definition get_naf_w3_partial_solve_wit_14_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (S: Z) (retval: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) ))) (PreH6 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0)) (PreH7 : ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4)) (PreH8 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0)) (PreH9 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH10 : (x3_2 < U64_MOD)) (PreH11 : (0 <= x3_2)) (PreH12 : (x2_2 < U64_MOD)) (PreH13 : (0 <= x2_2)) (PreH14 : (x1_2 < U64_MOD)) (PreH15 : (0 <= x1_2)) (PreH16 : (x0_2 < U64_MOD)) (PreH17 : (0 <= x0_2)) (PreH18 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH19 : (x3 < U64_MOD)) (PreH20 : (0 <= x3)) (PreH21 : (x2 < U64_MOD)) (PreH22 : (0 <= x2)) (PreH23 : (x1 < U64_MOD)) (PreH24 : (0 <= x1)) (PreH25 : (x0 < U64_MOD)) (PreH26 : (0 <= x0)) (PreH27 : (i < 257)) (PreH28 : (0 <= i)) (PreH29 : (i <= 257)) (PreH30 : (i = (Zlength (digits)))) (PreH31 : (0 <= Kcur)) (PreH32 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH33 : ((i >= 257) -> (Kcur = 0))) (PreH34 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH35 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH36 : (wnaf3_separated digits )) (PreH37 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH38 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH39 : (0 <= X)) (PreH40 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "k" ) ) S )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) ) = (S + (retval * U256_MOD ) )) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 0) ” 
  &&  “ ((Z.land (signed_last_nbits (x0_2) (8)) 7) < 4) ” 
  &&  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) <> 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) S )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons ((Z.land (signed_last_nbits (x0_2) (8)) 7)) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (store_u256 ( &( "x" ) ) (u256_of_limbs ((unsigned_last_nbits ((-(Z.land (signed_last_nbits (x0_2) (8)) 7))) (64))) (x1) (x2) (x3)) )
  **  (store_fn pk_pre K_non_alias )
.

Definition get_naf_w3_partial_solve_wit_15_non_alias := 
forall (naf_w3_pre: Z) (pk_pre: Z) (K_non_alias: Z) (X: Z) (Kcur: Z) (digits: (@list Z)) (i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0)) (PreH2 : (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH3 : (x3_2 < U64_MOD)) (PreH4 : (0 <= x3_2)) (PreH5 : (x2_2 < U64_MOD)) (PreH6 : (0 <= x2_2)) (PreH7 : (x1_2 < U64_MOD)) (PreH8 : (0 <= x1_2)) (PreH9 : (x0_2 < U64_MOD)) (PreH10 : (0 <= x0_2)) (PreH11 : (X = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH12 : (x3 < U64_MOD)) (PreH13 : (0 <= x3)) (PreH14 : (x2 < U64_MOD)) (PreH15 : (0 <= x2)) (PreH16 : (x1 < U64_MOD)) (PreH17 : (0 <= x1)) (PreH18 : (x0 < U64_MOD)) (PreH19 : (0 <= x0)) (PreH20 : (i < 257)) (PreH21 : (0 <= i)) (PreH22 : (i <= 257)) (PreH23 : (i = (Zlength (digits)))) (PreH24 : (0 <= Kcur)) (PreH25 : ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i )))))) (PreH26 : ((i >= 257) -> (Kcur = 0))) (PreH27 : (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) ))) (PreH28 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) ))) (PreH29 : (wnaf3_separated digits )) (PreH30 : (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0))) (PreH31 : (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0))) (PreH32 : (0 <= X)) (PreH33 : (X < U64_MOD)) ,
  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (((&(( &( "k" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "k" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fn pk_pre K_non_alias )
|--
  “ ((Z.land (Z.land (signed_last_nbits (x0_2) (8)) 7) 1) = 0) ” 
  &&  “ (Kcur = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i < 257) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 257) ” 
  &&  “ (i = (Zlength (digits))) ” 
  &&  “ (0 <= Kcur) ” 
  &&  “ ((i <= 256) -> (Kcur <= (Z.pow (2) ((256 - i ))))) ” 
  &&  “ ((i >= 257) -> (Kcur = 0)) ” 
  &&  “ (K_non_alias = ((wnaf3_value (digits)) + (Kcur * (Z.pow (2) (i)) ) )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> (wnaf3_digit (Znth (j) (digits) (0)) )) ” 
  &&  “ (wnaf3_separated digits ) ” 
  &&  “ (((i >= 1) /\ ((Znth ((i - 1 )) (digits) (0)) <> 0)) -> ((Kcur % ( 4 ) ) = 0)) ” 
  &&  “ (((i >= 2) /\ ((Znth ((i - 2 )) (digits) (0)) <> 0)) -> ((Kcur % ( 2 ) ) = 0)) ” 
  &&  “ (0 <= X) ” 
  &&  “ (X < U64_MOD) ”
  &&  (store_u256 ( &( "k" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (CharArray.full naf_w3_pre (i + 1 ) (app (digits) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg naf_w3_pre (i + 1 ) 257 )
  **  (((&(( &( "x" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "x" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "x" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "x" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fn pk_pre K_non_alias )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.

Axiom proof_of_get_naf_w3_safety_wit_1_non_alias : get_naf_w3_safety_wit_1_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_2_non_alias : get_naf_w3_safety_wit_2_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_3_non_alias : get_naf_w3_safety_wit_3_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_4_non_alias : get_naf_w3_safety_wit_4_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_5_non_alias : get_naf_w3_safety_wit_5_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_6_non_alias : get_naf_w3_safety_wit_6_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_7_non_alias : get_naf_w3_safety_wit_7_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_8_non_alias : get_naf_w3_safety_wit_8_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_9_non_alias : get_naf_w3_safety_wit_9_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_10_non_alias : get_naf_w3_safety_wit_10_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_11_non_alias : get_naf_w3_safety_wit_11_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_12_non_alias : get_naf_w3_safety_wit_12_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_13_non_alias : get_naf_w3_safety_wit_13_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_14_non_alias : get_naf_w3_safety_wit_14_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_15_non_alias : get_naf_w3_safety_wit_15_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_16_non_alias : get_naf_w3_safety_wit_16_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_17_non_alias : get_naf_w3_safety_wit_17_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_18_non_alias : get_naf_w3_safety_wit_18_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_19_non_alias : get_naf_w3_safety_wit_19_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_20_non_alias : get_naf_w3_safety_wit_20_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_21_non_alias : get_naf_w3_safety_wit_21_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_22_non_alias : get_naf_w3_safety_wit_22_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_23_non_alias : get_naf_w3_safety_wit_23_non_alias.
Axiom proof_of_get_naf_w3_safety_wit_24_non_alias : get_naf_w3_safety_wit_24_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_1_non_alias : get_naf_w3_entail_wit_1_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_2_non_alias : get_naf_w3_entail_wit_2_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_3_1_non_alias : get_naf_w3_entail_wit_3_1_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_3_2_non_alias : get_naf_w3_entail_wit_3_2_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_4_1_non_alias : get_naf_w3_entail_wit_4_1_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_4_2_non_alias : get_naf_w3_entail_wit_4_2_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_5_1_non_alias : get_naf_w3_entail_wit_5_1_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_5_2_non_alias : get_naf_w3_entail_wit_5_2_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_5_3_non_alias : get_naf_w3_entail_wit_5_3_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_5_4_non_alias : get_naf_w3_entail_wit_5_4_non_alias.
Axiom proof_of_get_naf_w3_entail_wit_5_5_non_alias : get_naf_w3_entail_wit_5_5_non_alias.
Axiom proof_of_get_naf_w3_return_wit_1_non_alias : get_naf_w3_return_wit_1_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_1_non_alias_pure : get_naf_w3_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_get_naf_w3_partial_solve_wit_1_non_alias : get_naf_w3_partial_solve_wit_1_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_2_non_alias_pure : get_naf_w3_partial_solve_wit_2_non_alias_pure.
Axiom proof_of_get_naf_w3_partial_solve_wit_2_non_alias : get_naf_w3_partial_solve_wit_2_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_3_non_alias_pure : get_naf_w3_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_get_naf_w3_partial_solve_wit_3_non_alias : get_naf_w3_partial_solve_wit_3_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_4_non_alias_pure : get_naf_w3_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_get_naf_w3_partial_solve_wit_4_non_alias : get_naf_w3_partial_solve_wit_4_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_5_non_alias_pure : get_naf_w3_partial_solve_wit_5_non_alias_pure.
Axiom proof_of_get_naf_w3_partial_solve_wit_5_non_alias : get_naf_w3_partial_solve_wit_5_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_6_non_alias : get_naf_w3_partial_solve_wit_6_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_7_non_alias : get_naf_w3_partial_solve_wit_7_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_8_non_alias : get_naf_w3_partial_solve_wit_8_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_9_non_alias : get_naf_w3_partial_solve_wit_9_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_10_non_alias : get_naf_w3_partial_solve_wit_10_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_11_non_alias : get_naf_w3_partial_solve_wit_11_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_12_non_alias : get_naf_w3_partial_solve_wit_12_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_13_non_alias : get_naf_w3_partial_solve_wit_13_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_14_non_alias : get_naf_w3_partial_solve_wit_14_non_alias.
Axiom proof_of_get_naf_w3_partial_solve_wit_15_non_alias : get_naf_w3_partial_solve_wit_15_non_alias.

End VC_Correct.
