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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function MontgInvModp -----*)

Definition MontgInvModp_safety_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "k" ) )) # UInt64  |->_)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "k" ) )) # UInt64  |->_)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "i" ) )) # UInt64  |->_)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "i" ) )) # UInt64  |->_)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_5_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_6_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "carry" ) )) # UChar  |->_)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_7_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_8_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_9_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_10_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_11_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "u" ) ))) (PreH2 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH3 : (A_non_alias <> 0)) ,
  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_12_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (PreH1 : (retval = ( &( "u" ) ))) (PreH2 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH3 : (result_pre = a_pre)) (PreH4 : (A_in_place <> 0)) ,
  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_13_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (A_non_alias <> 0)) ,
  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_14_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (A_non_alias <> 0)) ,
  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_15_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (result_pre = a_pre)) (PreH5 : (A_in_place <> 0)) ,
  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_16_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (result_pre = a_pre)) (PreH5 : (A_in_place <> 0)) ,
  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_17_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (A_non_alias <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_18_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (A_non_alias <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_19_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (result_pre = a_pre)) (PreH6 : (A_in_place <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_20_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (result_pre = a_pre)) (PreH6 : (A_in_place <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_21_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (A_non_alias <> 0)) ,
  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_22_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (result_pre = a_pre)) (PreH43 : (A_in_place <> 0)) ,
  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_23_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (A_non_alias <> 0)) ,
  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_24_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (result_pre = a_pre)) (PreH43 : (A_in_place <> 0)) ,
  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_25_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "v" ) ) Vn )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_26_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (Vn <> 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "v" ) ) Vn )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_27_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_u256 ( &( "v" ) ) Vi )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_28_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (Vi <> 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_u256 ( &( "v" ) ) Vi )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_29_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval = 0)) (PreH38 : (0 <= retval)) (PreH39 : (retval <= 1)) (PreH40 : (retval = 0)) (PreH41 : (Vn <> 0)) (PreH42 : (i = 0)) (PreH43 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_30_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval = 0)) (PreH38 : (0 <= retval)) (PreH39 : (retval <= 1)) (PreH40 : (retval = 0)) (PreH41 : (Vi <> 0)) (PreH42 : (result_pre = a_pre)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_31_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval = 0)) (PreH38 : (0 <= retval)) (PreH39 : (retval <= 1)) (PreH40 : (retval = 0)) (PreH41 : (Vi <> 0)) (PreH42 : (result_pre = a_pre)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_32_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval = 0)) (PreH38 : (0 <= retval)) (PreH39 : (retval <= 1)) (PreH40 : (retval = 0)) (PreH41 : (Vn <> 0)) (PreH42 : (i = 0)) (PreH43 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_33_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval = 0)) (PreH38 : (0 <= retval)) (PreH39 : (retval <= 1)) (PreH40 : (retval = 0)) (PreH41 : (Vi <> 0)) (PreH42 : (result_pre = a_pre)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_34_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval = 0)) (PreH38 : (0 <= retval)) (PreH39 : (retval <= 1)) (PreH40 : (retval = 0)) (PreH41 : (Vn <> 0)) (PreH42 : (i = 0)) (PreH43 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_35_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) <> 0)) (PreH2 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vi <> 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_36_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) <> 0)) (PreH2 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vn <> 0)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_37_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) <> 0)) (PreH2 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vn <> 0)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_38_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) <> 0)) (PreH2 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vi <> 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_39_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) <> 0)) (PreH2 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vn <> 0)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_40_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) <> 0)) (PreH2 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vi <> 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_41_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_42_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_43_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_44_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_45_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH7 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_46_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH8 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_47_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_48_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_49_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_50_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition MontgInvModp_safety_wit_51_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R5n: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (0 <= R5n)) (PreH7 : (R5n < SM2_P_Z)) (PreH8 : (sm2p_mont_inv_phase1_result A_non_alias R5n k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition MontgInvModp_safety_wit_52_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R5i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (0 <= R5i)) (PreH8 : (R5i < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_in_place R5i k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition MontgInvModp_safety_wit_53_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= K0n)) (PreH5 : (K0n <= 512)) (PreH6 : (K0n <> 256)) (PreH7 : (0 <= R5n)) (PreH8 : (R5n < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0n)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_54_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= K0n)) (PreH5 : (K0n <= 512)) (PreH6 : (K0n <> 256)) (PreH7 : (0 <= R5n)) (PreH8 : (R5n < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0n)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_55_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0i)) (PreH6 : (K0i <= 512)) (PreH7 : (K0i <> 256)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0i)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition MontgInvModp_safety_wit_56_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0i)) (PreH6 : (K0i <= 512)) (PreH7 : (K0i <> 256)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0i)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_57_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0n)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ ((2 * 256 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * 256 )) ”
.

Definition MontgInvModp_safety_wit_58_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0n)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition MontgInvModp_safety_wit_59_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0n)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition MontgInvModp_safety_wit_60_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0i)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ ((2 * 256 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * 256 )) ”
.

Definition MontgInvModp_safety_wit_61_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0i)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition MontgInvModp_safety_wit_62_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0i)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition MontgInvModp_safety_wit_63_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0n ))
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (64 <> 0) ”
.

Definition MontgInvModp_safety_wit_64_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0n ))
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition MontgInvModp_safety_wit_65_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0i ))
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (64 <> 0) ”
.

Definition MontgInvModp_safety_wit_66_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0i ))
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition MontgInvModp_safety_wit_67_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> (((2 * 256 ) - K0n ) ÷ 64 ))
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0n ))
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (64 <> 0) ”
.

Definition MontgInvModp_safety_wit_68_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> (((2 * 256 ) - K0n ) ÷ 64 ))
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0n ))
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition MontgInvModp_safety_wit_69_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> (((2 * 256 ) - K0i ) ÷ 64 ))
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0i ))
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (64 <> 0) ”
.

Definition MontgInvModp_safety_wit_70_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> (((2 * 256 ) - K0i ) ÷ 64 ))
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> ((2 * 256 ) - K0i ))
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition MontgInvModp_safety_wit_71_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
|--
  “ (k <= 63) ” 
  &&  “ (0 <= k) ”
.

Definition MontgInvModp_safety_wit_72_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_73_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
|--
  “ (k <= 63) ” 
  &&  “ (0 <= k) ”
.

Definition MontgInvModp_safety_wit_74_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition MontgInvModp_safety_wit_75_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (k = 256)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (i = 0)) (PreH5 : (0 <= R5n)) (PreH6 : (R5n < SM2_P_Z)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n 256 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_safety_wit_76_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5i)) (PreH7 : (R5i < SM2_P_Z)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i 256 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition MontgInvModp_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = ( &( "s" ) ))) (PreH2 : (retval_3 = ( &( "r" ) ))) (PreH3 : (retval_2 = ( &( "v" ) ))) (PreH4 : (retval = ( &( "u" ) ))) (PreH5 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH6 : (A_non_alias <> 0)) ,
  (store_u256 ( &( "s" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval_4 = ( &( "s" ) )) ” 
  &&  “ (retval_3 = ( &( "r" ) )) ” 
  &&  “ (retval_2 = ( &( "v" ) )) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_8: Z)  (retval_7: Z)  (retval_6: Z)  (retval_5: Z) ,
  “ (0 = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (SM2_P_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_8 = ( &( "s" ) )) ” 
  &&  “ (retval_7 = ( &( "r" ) )) ” 
  &&  “ (retval_6 = ( &( "v" ) )) ” 
  &&  “ (retval_5 = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_1_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = ( &( "s" ) ))) (PreH2 : (retval_7 = ( &( "r" ) ))) (PreH3 : (retval_6 = ( &( "v" ) ))) (PreH4 : (retval_5 = ( &( "u" ) ))) (PreH5 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH6 : (result_pre = a_pre)) (PreH7 : (A_in_place <> 0)) ,
  (store_u256 ( &( "s" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval_4: Z)  (retval_3: Z)  (retval_2: Z)  (retval: Z) ,
  “ (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
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
  &&  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval_4 = ( &( "s" ) )) ” 
  &&  “ (retval_3 = ( &( "r" ) )) ” 
  &&  “ (retval_2 = ( &( "v" ) )) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (0 = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (A_in_place = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (SM2_P_Z = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_8 = ( &( "s" ) )) ” 
  &&  “ (retval_7 = ( &( "r" ) )) ” 
  &&  “ (retval_6 = ( &( "v" ) )) ” 
  &&  “ (retval_5 = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (A_non_alias <> 0)) ,
  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  EX (Un: Z)  (Vn: Z)  (Rn: Z)  (Sn: Z) ,
  “ (0 = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn 0 0 ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (A_non_alias <> 0)) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_state A_non_alias SM2_P_Z A_non_alias 0 (u256_of_limbs (1) (x1_4) (x2_4) (x3_4)) 0 0 ) ” 
  &&  “ (1 < U64_MOD) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_2_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (A_non_alias <> 0)) ,
  (sm2p_mont_inv_phase1_state A_non_alias SM2_P_Z A_non_alias 0 (u256_of_limbs (1) (x1_4) (x2_4) (x3_4)) 0 0 )
.

Definition MontgInvModp_entail_wit_2_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (A_non_alias <> 0)) ,
  (1 < U64_MOD)
.

Definition MontgInvModp_entail_wit_3_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (result_pre = a_pre)) (PreH43 : (A_in_place <> 0)) ,
  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Ui: Z)  (Vi: Z)  (Ri: Z)  (Si: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si 0 0 ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (result_pre = a_pre)) (PreH43 : (A_in_place <> 0)) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_state A_in_place SM2_P_Z A_in_place 0 (u256_of_limbs (1) (x1_4) (x2_4) (x3_4)) 0 0 ) ” 
  &&  “ (1 < U64_MOD) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_3_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (result_pre = a_pre)) (PreH43 : (A_in_place <> 0)) ,
  (sm2p_mont_inv_phase1_state A_in_place SM2_P_Z A_in_place 0 (u256_of_limbs (1) (x1_4) (x2_4) (x3_4)) 0 0 )
.

Definition MontgInvModp_entail_wit_3_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (A_in_place = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (retval_4 = ( &( "s" ) ))) (PreH38 : (retval_3 = ( &( "r" ) ))) (PreH39 : (retval_2 = ( &( "v" ) ))) (PreH40 : (retval = ( &( "u" ) ))) (PreH41 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH42 : (result_pre = a_pre)) (PreH43 : (A_in_place <> 0)) ,
  (1 < U64_MOD)
.

Definition MontgInvModp_entail_wit_4_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (Vn <> 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "v" ) ) Vn )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_2: Z)  (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k_2 carry_2 ) ”
  &&  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_4_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k_2: Z) (carry_2: Z) (i_2: Z) (retval_2: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (Vi <> 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i_2 = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k_2 carry_2 )) ,
  (store_u256 ( &( "v" ) ) Vi )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z)  (k: Z)  (carry: Z)  (i: Z) ,
  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k_2 carry_2 ) ”
  &&  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_5_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0) (x1) (x2) (x3)) Y retval_2 )) (PreH2 : ((Z.land x0_3 1) = 0)) (PreH3 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vn <> 0)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "s" ) ) Y )
  **  (store_u256 ( &( "u" ) ) ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ÷ 2 ) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (S2: Z) ,
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias (Un ÷ 2 ) Vn Rn S2 (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Un ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0) (x1) (x2) (x3)) Y retval_2 )) (PreH2 : ((Z.land x0_3 1) = 0)) (PreH3 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vn <> 0)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_state A_non_alias (Un ÷ 2 ) Vn Rn Y (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_5_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0) (x1) (x2) (x3)) Y retval_2 )) (PreH2 : ((Z.land x0_3 1) = 0)) (PreH3 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vn <> 0)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (sm2p_mont_inv_phase1_state A_non_alias (Un ÷ 2 ) Vn Rn Y (unsigned_last_nbits ((k + 1 )) (64)) carry )
.

Definition MontgInvModp_entail_wit_6_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0) (x1) (x2) (x3)) Y retval_2 )) (PreH2 : ((Z.land x0_3 1) = 0)) (PreH3 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vi <> 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_u256 ( &( "s" ) ) Y )
  **  (store_u256 ( &( "u" ) ) ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ÷ 2 ) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (S2: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place (Ui ÷ 2 ) Vi Ri S2 (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Ui ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0) (x1) (x2) (x3)) Y retval_2 )) (PreH2 : ((Z.land x0_3 1) = 0)) (PreH3 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vi <> 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_state A_in_place (Ui ÷ 2 ) Vi Ri Y (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_6_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0) (x1) (x2) (x3)) Y retval_2 )) (PreH2 : ((Z.land x0_3 1) = 0)) (PreH3 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vi <> 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (sm2p_mont_inv_phase1_state A_in_place (Ui ÷ 2 ) Vi Ri Y (unsigned_last_nbits ((k + 1 )) (64)) carry )
.

Definition MontgInvModp_entail_wit_7_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) Y retval_2 )) (PreH2 : ((Z.land x0_4 1) = 0)) (PreH3 : ((Z.land x0_3 1) <> 0)) (PreH4 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : (x3_4 < U64_MOD)) (PreH6 : (0 <= x3_4)) (PreH7 : (x2_4 < U64_MOD)) (PreH8 : (0 <= x2_4)) (PreH9 : (x1_4 < U64_MOD)) (PreH10 : (0 <= x1_4)) (PreH11 : (x0_4 < U64_MOD)) (PreH12 : (0 <= x0_4)) (PreH13 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (retval = 0)) (PreH41 : (0 <= retval)) (PreH42 : (retval <= 1)) (PreH43 : (retval = 0)) (PreH44 : (Vn <> 0)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "r" ) ) Y )
  **  (store_u256 ( &( "v" ) ) ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ÷ 2 ) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2n: Z) ,
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un (Vn ÷ 2 ) R2n Sn (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) (Vn ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) Y retval_2 )) (PreH2 : ((Z.land x0_4 1) = 0)) (PreH3 : ((Z.land x0_3 1) <> 0)) (PreH4 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : (x3_4 < U64_MOD)) (PreH6 : (0 <= x3_4)) (PreH7 : (x2_4 < U64_MOD)) (PreH8 : (0 <= x2_4)) (PreH9 : (x1_4 < U64_MOD)) (PreH10 : (0 <= x1_4)) (PreH11 : (x0_4 < U64_MOD)) (PreH12 : (0 <= x0_4)) (PreH13 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (retval = 0)) (PreH41 : (0 <= retval)) (PreH42 : (retval <= 1)) (PreH43 : (retval = 0)) (PreH44 : (Vn <> 0)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_state A_non_alias Un (Vn ÷ 2 ) Y Sn (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_7_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) Y retval_2 )) (PreH2 : ((Z.land x0_4 1) = 0)) (PreH3 : ((Z.land x0_3 1) <> 0)) (PreH4 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : (x3_4 < U64_MOD)) (PreH6 : (0 <= x3_4)) (PreH7 : (x2_4 < U64_MOD)) (PreH8 : (0 <= x2_4)) (PreH9 : (x1_4 < U64_MOD)) (PreH10 : (0 <= x1_4)) (PreH11 : (x0_4 < U64_MOD)) (PreH12 : (0 <= x0_4)) (PreH13 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (retval = 0)) (PreH41 : (0 <= retval)) (PreH42 : (retval <= 1)) (PreH43 : (retval = 0)) (PreH44 : (Vn <> 0)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (sm2p_mont_inv_phase1_state A_non_alias Un (Vn ÷ 2 ) Y Sn (unsigned_last_nbits ((k + 1 )) (64)) carry )
.

Definition MontgInvModp_entail_wit_8_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) Y retval_2 )) (PreH2 : ((Z.land x0_4 1) = 0)) (PreH3 : ((Z.land x0_3 1) <> 0)) (PreH4 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : (x3_4 < U64_MOD)) (PreH6 : (0 <= x3_4)) (PreH7 : (x2_4 < U64_MOD)) (PreH8 : (0 <= x2_4)) (PreH9 : (x1_4 < U64_MOD)) (PreH10 : (0 <= x1_4)) (PreH11 : (x0_4 < U64_MOD)) (PreH12 : (0 <= x0_4)) (PreH13 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (retval = 0)) (PreH41 : (0 <= retval)) (PreH42 : (retval <= 1)) (PreH43 : (retval = 0)) (PreH44 : (Vi <> 0)) (PreH45 : (result_pre = a_pre)) (PreH46 : (i = 0)) (PreH47 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_u256 ( &( "r" ) ) Y )
  **  (store_u256 ( &( "v" ) ) ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ÷ 2 ) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2i: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui (Vi ÷ 2 ) R2i Si (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) (Vi ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) Y retval_2 )) (PreH2 : ((Z.land x0_4 1) = 0)) (PreH3 : ((Z.land x0_3 1) <> 0)) (PreH4 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : (x3_4 < U64_MOD)) (PreH6 : (0 <= x3_4)) (PreH7 : (x2_4 < U64_MOD)) (PreH8 : (0 <= x2_4)) (PreH9 : (x1_4 < U64_MOD)) (PreH10 : (0 <= x1_4)) (PreH11 : (x0_4 < U64_MOD)) (PreH12 : (0 <= x0_4)) (PreH13 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (retval = 0)) (PreH41 : (0 <= retval)) (PreH42 : (retval <= 1)) (PreH43 : (retval = 0)) (PreH44 : (Vi <> 0)) (PreH45 : (result_pre = a_pre)) (PreH46 : (i = 0)) (PreH47 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_state A_in_place Ui (Vi ÷ 2 ) Y Si (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_8_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (Y: Z) (retval_2: Z) (PreH1 : (u256_shl_result (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) Y retval_2 )) (PreH2 : ((Z.land x0_4 1) = 0)) (PreH3 : ((Z.land x0_3 1) <> 0)) (PreH4 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : (x3_4 < U64_MOD)) (PreH6 : (0 <= x3_4)) (PreH7 : (x2_4 < U64_MOD)) (PreH8 : (0 <= x2_4)) (PreH9 : (x1_4 < U64_MOD)) (PreH10 : (0 <= x1_4)) (PreH11 : (x0_4 < U64_MOD)) (PreH12 : (0 <= x0_4)) (PreH13 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH14 : (x3_3 < U64_MOD)) (PreH15 : (0 <= x3_3)) (PreH16 : (x2_3 < U64_MOD)) (PreH17 : (0 <= x2_3)) (PreH18 : (x1_3 < U64_MOD)) (PreH19 : (0 <= x1_3)) (PreH20 : (x0_3 < U64_MOD)) (PreH21 : (0 <= x0_3)) (PreH22 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH23 : (x3_2 < U64_MOD)) (PreH24 : (0 <= x3_2)) (PreH25 : (x2_2 < U64_MOD)) (PreH26 : (0 <= x2_2)) (PreH27 : (x1_2 < U64_MOD)) (PreH28 : (0 <= x1_2)) (PreH29 : (x0_2 < U64_MOD)) (PreH30 : (0 <= x0_2)) (PreH31 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH32 : (x3 < U64_MOD)) (PreH33 : (0 <= x3)) (PreH34 : (x2 < U64_MOD)) (PreH35 : (0 <= x2)) (PreH36 : (x1 < U64_MOD)) (PreH37 : (0 <= x1)) (PreH38 : (x0 < U64_MOD)) (PreH39 : (0 <= x0)) (PreH40 : (retval = 0)) (PreH41 : (0 <= retval)) (PreH42 : (retval <= 1)) (PreH43 : (retval = 0)) (PreH44 : (Vi <> 0)) (PreH45 : (result_pre = a_pre)) (PreH46 : (i = 0)) (PreH47 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (sm2p_mont_inv_phase1_state A_in_place Ui (Vi ÷ 2 ) Y Si (unsigned_last_nbits ((k + 1 )) (64)) carry )
.

Definition MontgInvModp_entail_wit_9_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_5 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <= (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_9_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <= (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_9_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval_3: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) > (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH5 : ((Z.land x0_8 1) <> 0)) (PreH6 : ((Z.land x0_7 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH8 : (x3_8 < U64_MOD)) (PreH9 : (0 <= x3_8)) (PreH10 : (x2_8 < U64_MOD)) (PreH11 : (0 <= x2_8)) (PreH12 : (x1_8 < U64_MOD)) (PreH13 : (0 <= x1_8)) (PreH14 : (x0_8 < U64_MOD)) (PreH15 : (0 <= x0_8)) (PreH16 : (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH17 : (x3_7 < U64_MOD)) (PreH18 : (0 <= x3_7)) (PreH19 : (x2_7 < U64_MOD)) (PreH20 : (0 <= x2_7)) (PreH21 : (x1_7 < U64_MOD)) (PreH22 : (0 <= x1_7)) (PreH23 : (x0_7 < U64_MOD)) (PreH24 : (0 <= x0_7)) (PreH25 : (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH26 : (x3_6 < U64_MOD)) (PreH27 : (0 <= x3_6)) (PreH28 : (x2_6 < U64_MOD)) (PreH29 : (0 <= x2_6)) (PreH30 : (x1_6 < U64_MOD)) (PreH31 : (0 <= x1_6)) (PreH32 : (x0_6 < U64_MOD)) (PreH33 : (0 <= x0_6)) (PreH34 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH35 : (x3_5 < U64_MOD)) (PreH36 : (0 <= x3_5)) (PreH37 : (x2_5 < U64_MOD)) (PreH38 : (0 <= x2_5)) (PreH39 : (x1_5 < U64_MOD)) (PreH40 : (0 <= x1_5)) (PreH41 : (x0_5 < U64_MOD)) (PreH42 : (0 <= x0_5)) (PreH43 : (retval_3 = 0)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (retval_3 = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_5 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <= (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_9_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval_3: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <= (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH5 : ((Z.land x0_8 1) <> 0)) (PreH6 : ((Z.land x0_7 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH8 : (x3_8 < U64_MOD)) (PreH9 : (0 <= x3_8)) (PreH10 : (x2_8 < U64_MOD)) (PreH11 : (0 <= x2_8)) (PreH12 : (x1_8 < U64_MOD)) (PreH13 : (0 <= x1_8)) (PreH14 : (x0_8 < U64_MOD)) (PreH15 : (0 <= x0_8)) (PreH16 : (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH17 : (x3_7 < U64_MOD)) (PreH18 : (0 <= x3_7)) (PreH19 : (x2_7 < U64_MOD)) (PreH20 : (0 <= x2_7)) (PreH21 : (x1_7 < U64_MOD)) (PreH22 : (0 <= x1_7)) (PreH23 : (x0_7 < U64_MOD)) (PreH24 : (0 <= x0_7)) (PreH25 : (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH26 : (x3_6 < U64_MOD)) (PreH27 : (0 <= x3_6)) (PreH28 : (x2_6 < U64_MOD)) (PreH29 : (0 <= x2_6)) (PreH30 : (x1_6 < U64_MOD)) (PreH31 : (0 <= x1_6)) (PreH32 : (x0_6 < U64_MOD)) (PreH33 : (0 <= x0_6)) (PreH34 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH35 : (x3_5 < U64_MOD)) (PreH36 : (0 <= x3_5)) (PreH37 : (x2_5 < U64_MOD)) (PreH38 : (0 <= x2_5)) (PreH39 : (x1_5 < U64_MOD)) (PreH40 : (0 <= x1_5)) (PreH41 : (x0_5 < U64_MOD)) (PreH42 : (0 <= x0_5)) (PreH43 : (retval_3 = 0)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (retval_3 = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_4 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <= (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_10_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) > (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_10_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_5 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) > (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_10_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval_3: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 1)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) > (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH5 : ((Z.land x0_8 1) <> 0)) (PreH6 : ((Z.land x0_7 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH8 : (x3_8 < U64_MOD)) (PreH9 : (0 <= x3_8)) (PreH10 : (x2_8 < U64_MOD)) (PreH11 : (0 <= x2_8)) (PreH12 : (x1_8 < U64_MOD)) (PreH13 : (0 <= x1_8)) (PreH14 : (x0_8 < U64_MOD)) (PreH15 : (0 <= x0_8)) (PreH16 : (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH17 : (x3_7 < U64_MOD)) (PreH18 : (0 <= x3_7)) (PreH19 : (x2_7 < U64_MOD)) (PreH20 : (0 <= x2_7)) (PreH21 : (x1_7 < U64_MOD)) (PreH22 : (0 <= x1_7)) (PreH23 : (x0_7 < U64_MOD)) (PreH24 : (0 <= x0_7)) (PreH25 : (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH26 : (x3_6 < U64_MOD)) (PreH27 : (0 <= x3_6)) (PreH28 : (x2_6 < U64_MOD)) (PreH29 : (0 <= x2_6)) (PreH30 : (x1_6 < U64_MOD)) (PreH31 : (0 <= x1_6)) (PreH32 : (x0_6 < U64_MOD)) (PreH33 : (0 <= x0_6)) (PreH34 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH35 : (x3_5 < U64_MOD)) (PreH36 : (0 <= x3_5)) (PreH37 : (x2_5 < U64_MOD)) (PreH38 : (0 <= x2_5)) (PreH39 : (x1_5 < U64_MOD)) (PreH40 : (0 <= x1_5)) (PreH41 : (x0_5 < U64_MOD)) (PreH42 : (0 <= x0_5)) (PreH43 : (retval_3 = 0)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (retval_3 = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_4 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) > (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_10_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval_3: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) <= (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH5 : ((Z.land x0_8 1) <> 0)) (PreH6 : ((Z.land x0_7 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH8 : (x3_8 < U64_MOD)) (PreH9 : (0 <= x3_8)) (PreH10 : (x2_8 < U64_MOD)) (PreH11 : (0 <= x2_8)) (PreH12 : (x1_8 < U64_MOD)) (PreH13 : (0 <= x1_8)) (PreH14 : (x0_8 < U64_MOD)) (PreH15 : (0 <= x0_8)) (PreH16 : (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH17 : (x3_7 < U64_MOD)) (PreH18 : (0 <= x3_7)) (PreH19 : (x2_7 < U64_MOD)) (PreH20 : (0 <= x2_7)) (PreH21 : (x1_7 < U64_MOD)) (PreH22 : (0 <= x1_7)) (PreH23 : (x0_7 < U64_MOD)) (PreH24 : (0 <= x0_7)) (PreH25 : (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH26 : (x3_6 < U64_MOD)) (PreH27 : (0 <= x3_6)) (PreH28 : (x2_6 < U64_MOD)) (PreH29 : (0 <= x2_6)) (PreH30 : (x1_6 < U64_MOD)) (PreH31 : (0 <= x1_6)) (PreH32 : (x0_6 < U64_MOD)) (PreH33 : (0 <= x0_6)) (PreH34 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH35 : (x3_5 < U64_MOD)) (PreH36 : (0 <= x3_5)) (PreH37 : (x2_5 < U64_MOD)) (PreH38 : (0 <= x2_5)) (PreH39 : (x1_5 < U64_MOD)) (PreH40 : (0 <= x1_5)) (PreH41 : (x0_5 < U64_MOD)) (PreH42 : (0 <= x0_5)) (PreH43 : (retval_3 = 0)) (PreH44 : (0 <= retval_3)) (PreH45 : (retval_3 <= 1)) (PreH46 : (retval_3 = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_5 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval_2: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) > (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ ((Z.land x0_8 1) <> 0) ” 
  &&  “ ((Z.land x0_7 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Ui = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_11_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_3: Z) (Y: Z) (retval_4: Z) (PreH1 : (u256_shl_result Sn Y retval_4 )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 <= 1)) (PreH6 : ((Rn + Sn ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Un - Vn ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vn <> 0)) (PreH59 : (i = 0)) (PreH60 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH61 : (retval_2 <> 0)) ,
  (store_u256 ( &( "s" ) ) Y )
  **  (store_u256 ( &( "r" ) ) S_2 )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (S2: Z)  (add_carry: Z)  (Rsum: Z)  (borrow: Z)  (Usub: Z) ,
  “ (i = 0) ” 
  &&  “ (Un > Vn) ” 
  &&  “ (0 <= Usub) ” 
  &&  “ (Usub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Un - Vn ) = (Usub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= Rsum) ” 
  &&  “ (Rsum < U256_MOD) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ ((Rn + Sn ) = (Rsum + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias (Usub ÷ 2 ) Vn Rsum S2 (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Usub ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rsum )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_3: Z) (Y: Z) (retval_4: Z) (PreH1 : (u256_shl_result Sn Y retval_4 )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 <= 1)) (PreH6 : ((Rn + Sn ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Un - Vn ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vn <> 0)) (PreH59 : (i = 0)) (PreH60 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH61 : (retval_2 <> 0)) ,
  TT && emp 
|--
  EX (add_carry: Z)  (borrow: Z)  (Usub: Z) ,
  “ ((S ÷ 2 ) = (Usub ÷ 2 )) ” 
  &&  “ (0 <= Usub) ” 
  &&  “ (Usub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) - (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ) = (Usub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs (x0) (x1) (x2) (x3)) ) = (S_2 + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias (Usub ÷ 2 ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) S_2 Y (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_12_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_3: Z) (Y: Z) (retval_4: Z) (PreH1 : (u256_shl_result Si Y retval_4 )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 <= 1)) (PreH6 : ((Ri + Si ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Ui - Vi ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vi <> 0)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH62 : (retval_2 <> 0)) ,
  (store_u256 ( &( "s" ) ) Y )
  **  (store_u256 ( &( "r" ) ) S_2 )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (S2: Z)  (add_carry: Z)  (Rsum: Z)  (borrow: Z)  (Usub: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (Ui > Vi) ” 
  &&  “ (0 <= Usub) ” 
  &&  “ (Usub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Ui - Vi ) = (Usub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= Rsum) ” 
  &&  “ (Rsum < U256_MOD) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ ((Ri + Si ) = (Rsum + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place (Usub ÷ 2 ) Vi Rsum S2 (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Usub ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Rsum )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_3: Z) (Y: Z) (retval_4: Z) (PreH1 : (u256_shl_result Si Y retval_4 )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_3)) (PreH5 : (retval_3 <= 1)) (PreH6 : ((Ri + Si ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Ui - Vi ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vi <> 0)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH62 : (retval_2 <> 0)) ,
  TT && emp 
|--
  EX (add_carry: Z)  (borrow: Z)  (Usub: Z) ,
  “ ((S ÷ 2 ) = (Usub ÷ 2 )) ” 
  &&  “ (0 <= Usub) ” 
  &&  “ (Usub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) - (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ) = (Usub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs (x0) (x1) (x2) (x3)) ) = (S_2 + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place (Usub ÷ 2 ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) S_2 Y (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_13_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval_2: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_3: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_4: Z) (Y: Z) (retval: Z) (PreH1 : (u256_shl_result Rn Y retval )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((Rn + Sn ) = (S_2 + (retval_4 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Vn - Un ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval_2 = 0)) (PreH55 : (0 <= retval_2)) (PreH56 : (retval_2 <= 1)) (PreH57 : (retval_2 = 0)) (PreH58 : (Vn <> 0)) (PreH59 : (i = 0)) (PreH60 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH61 : (retval_3 = 0)) ,
  (store_u256 ( &( "r" ) ) Y )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2n: Z)  (add_carry: Z)  (Ssum: Z)  (borrow: Z)  (Vsub: Z) ,
  “ (i = 0) ” 
  &&  “ (Un <= Vn) ” 
  &&  “ (0 <= Vsub) ” 
  &&  “ (Vsub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vn - Un ) = (Vsub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= Ssum) ” 
  &&  “ (Ssum < U256_MOD) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ ((Rn + Sn ) = (Ssum + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un (Vsub ÷ 2 ) R2n Ssum (unsigned_last_nbits ((k + 1 )) (64)) (unsigned_last_nbits ((carry + retval )) (8)) ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) (Vsub ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Ssum )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval_2: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_3: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_4: Z) (Y: Z) (retval: Z) (PreH1 : (u256_shl_result Rn Y retval )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((Rn + Sn ) = (S_2 + (retval_4 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Vn - Un ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval_2 = 0)) (PreH55 : (0 <= retval_2)) (PreH56 : (retval_2 <= 1)) (PreH57 : (retval_2 = 0)) (PreH58 : (Vn <> 0)) (PreH59 : (i = 0)) (PreH60 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH61 : (retval_3 = 0)) ,
  TT && emp 
|--
  EX (add_carry: Z)  (borrow: Z)  (Vsub: Z) ,
  “ ((S ÷ 2 ) = (Vsub ÷ 2 )) ” 
  &&  “ (0 <= Vsub) ” 
  &&  “ (Vsub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) - (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (Vsub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs (x0) (x1) (x2) (x3)) ) = (S_2 + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (Vsub ÷ 2 ) Y S_2 (unsigned_last_nbits ((k + 1 )) (64)) (unsigned_last_nbits ((carry + retval )) (8)) ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_14_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval_2: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_3: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_4: Z) (Y: Z) (retval: Z) (PreH1 : (u256_shl_result Ri Y retval )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((Ri + Si ) = (S_2 + (retval_4 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Vi - Ui ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval_2 = 0)) (PreH55 : (0 <= retval_2)) (PreH56 : (retval_2 <= 1)) (PreH57 : (retval_2 = 0)) (PreH58 : (Vi <> 0)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH62 : (retval_3 = 0)) ,
  (store_u256 ( &( "r" ) ) Y )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2i: Z)  (add_carry: Z)  (Ssum: Z)  (borrow: Z)  (Vsub: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (Ui <= Vi) ” 
  &&  “ (0 <= Vsub) ” 
  &&  “ (Vsub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vi - Ui ) = (Vsub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= Ssum) ” 
  &&  “ (Ssum < U256_MOD) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ ((Ri + Si ) = (Ssum + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui (Vsub ÷ 2 ) R2i Ssum (unsigned_last_nbits ((k + 1 )) (64)) (unsigned_last_nbits ((carry + retval )) (8)) ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) (Vsub ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Ssum )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval_2: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_3: Z) (borrow_2: Z) (S: Z) (S_2: Z) (retval_4: Z) (Y: Z) (retval: Z) (PreH1 : (u256_shl_result Ri Y retval )) (PreH2 : (0 <= S_2)) (PreH3 : (S_2 < U256_MOD)) (PreH4 : (0 <= retval_4)) (PreH5 : (retval_4 <= 1)) (PreH6 : ((Ri + Si ) = (S_2 + (retval_4 * U256_MOD ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow_2)) (PreH10 : (borrow_2 <= 1)) (PreH11 : ((Vi - Ui ) = (S - (borrow_2 * U256_MOD ) ))) (PreH12 : (0 <= retval_3)) (PreH13 : (retval_3 <= 1)) (PreH14 : (retval_3 = 0)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval_2 = 0)) (PreH55 : (0 <= retval_2)) (PreH56 : (retval_2 <= 1)) (PreH57 : (retval_2 = 0)) (PreH58 : (Vi <> 0)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH62 : (retval_3 = 0)) ,
  TT && emp 
|--
  EX (add_carry: Z)  (borrow: Z)  (Vsub: Z) ,
  “ ((S ÷ 2 ) = (Vsub ÷ 2 )) ” 
  &&  “ (0 <= Vsub) ” 
  &&  “ (Vsub < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ (((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) - (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ) = (Vsub - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= add_carry) ” 
  &&  “ (add_carry <= 1) ” 
  &&  “ (((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) + (u256_of_limbs (x0) (x1) (x2) (x3)) ) = (S_2 + (add_carry * U256_MOD ) )) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (Vsub ÷ 2 ) Y S_2 (unsigned_last_nbits ((k + 1 )) (64)) (unsigned_last_nbits ((carry + retval )) (8)) ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_15_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi_2: Z) (Ri_2: Z) (Si_2: Z) (S2: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi_2 Ri_2 Si_2 k carry )) (PreH4 : (sm2p_mont_inv_phase1_state A_in_place (Ui_2 ÷ 2 ) Vi_2 Ri_2 S2 (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Ui_2 ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi_2 )
  **  (store_u256 ( &( "r" ) ) Ri_2 )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Ui: Z)  (Vi: Z)  (Ri: Z)  (Si: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_15_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi_2: Z) (Ri_2: Z) (Si_2: Z) (R2i: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi_2 Ri_2 Si_2 k carry )) (PreH4 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 (Vi_2 ÷ 2 ) R2i Si_2 (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui_2 )
  **  (store_u256 ( &( "v" ) ) (Vi_2 ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si_2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Ui: Z)  (Vi: Z)  (Ri: Z)  (Si: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_15_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi_2: Z) (Ri_2: Z) (Si_2: Z) (Usub: Z) (borrow: Z) (Rsum: Z) (add_carry: Z) (S2: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (Ui_2 > Vi_2)) (PreH4 : (0 <= Usub)) (PreH5 : (Usub < U256_MOD)) (PreH6 : (0 <= borrow)) (PreH7 : (borrow <= 1)) (PreH8 : ((Ui_2 - Vi_2 ) = (Usub - (borrow * U256_MOD ) ))) (PreH9 : (0 <= Rsum)) (PreH10 : (Rsum < U256_MOD)) (PreH11 : (0 <= add_carry)) (PreH12 : (add_carry <= 1)) (PreH13 : ((Ri_2 + Si_2 ) = (Rsum + (add_carry * U256_MOD ) ))) (PreH14 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi_2 Ri_2 Si_2 k carry )) (PreH15 : (sm2p_mont_inv_phase1_state A_in_place (Usub ÷ 2 ) Vi_2 Rsum S2 (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Usub ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi_2 )
  **  (store_u256 ( &( "r" ) ) Rsum )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Ui: Z)  (Vi: Z)  (Ri: Z)  (Si: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_15_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi_2: Z) (Ri_2: Z) (Si_2: Z) (Vsub: Z) (borrow: Z) (Ssum: Z) (add_carry: Z) (R2i: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (Ui_2 <= Vi_2)) (PreH4 : (0 <= Vsub)) (PreH5 : (Vsub < U256_MOD)) (PreH6 : (0 <= borrow)) (PreH7 : (borrow <= 1)) (PreH8 : ((Vi_2 - Ui_2 ) = (Vsub - (borrow * U256_MOD ) ))) (PreH9 : (0 <= Ssum)) (PreH10 : (Ssum < U256_MOD)) (PreH11 : (0 <= add_carry)) (PreH12 : (add_carry <= 1)) (PreH13 : ((Ri_2 + Si_2 ) = (Ssum + (add_carry * U256_MOD ) ))) (PreH14 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 (Vsub ÷ 2 ) R2i Ssum (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui_2 )
  **  (store_u256 ( &( "v" ) ) (Vsub ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Ssum )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Ui: Z)  (Vi: Z)  (Ri: Z)  (Si: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_16_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un_2: Z) (Vn_2: Z) (Rn_2: Z) (Sn_2: Z) (S2: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (i = 0)) (PreH2 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn_2 Rn_2 Sn_2 k carry )) (PreH3 : (sm2p_mont_inv_phase1_state A_non_alias (Un_2 ÷ 2 ) Vn_2 Rn_2 S2 (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Un_2 ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn_2 )
  **  (store_u256 ( &( "r" ) ) Rn_2 )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Un: Z)  (Vn: Z)  (Rn: Z)  (Sn: Z) ,
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_16_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un_2: Z) (Vn_2: Z) (Rn_2: Z) (Sn_2: Z) (R2n: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (i = 0)) (PreH2 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn_2 Rn_2 Sn_2 k carry )) (PreH3 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 (Vn_2 ÷ 2 ) R2n Sn_2 (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un_2 )
  **  (store_u256 ( &( "v" ) ) (Vn_2 ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn_2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Un: Z)  (Vn: Z)  (Rn: Z)  (Sn: Z) ,
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_16_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un_2: Z) (Vn_2: Z) (Rn_2: Z) (Sn_2: Z) (Usub: Z) (borrow: Z) (Rsum: Z) (add_carry: Z) (S2: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (i = 0)) (PreH2 : (Un_2 > Vn_2)) (PreH3 : (0 <= Usub)) (PreH4 : (Usub < U256_MOD)) (PreH5 : (0 <= borrow)) (PreH6 : (borrow <= 1)) (PreH7 : ((Un_2 - Vn_2 ) = (Usub - (borrow * U256_MOD ) ))) (PreH8 : (0 <= Rsum)) (PreH9 : (Rsum < U256_MOD)) (PreH10 : (0 <= add_carry)) (PreH11 : (add_carry <= 1)) (PreH12 : ((Rn_2 + Sn_2 ) = (Rsum + (add_carry * U256_MOD ) ))) (PreH13 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn_2 Rn_2 Sn_2 k carry )) (PreH14 : (sm2p_mont_inv_phase1_state A_non_alias (Usub ÷ 2 ) Vn_2 Rsum S2 (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) (Usub ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn_2 )
  **  (store_u256 ( &( "r" ) ) Rsum )
  **  (store_u256 ( &( "s" ) ) S2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Un: Z)  (Vn: Z)  (Rn: Z)  (Sn: Z) ,
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_16_4_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un_2: Z) (Vn_2: Z) (Rn_2: Z) (Sn_2: Z) (Vsub: Z) (borrow: Z) (Ssum: Z) (add_carry: Z) (R2n: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (i = 0)) (PreH2 : (Un_2 <= Vn_2)) (PreH3 : (0 <= Vsub)) (PreH4 : (Vsub < U256_MOD)) (PreH5 : (0 <= borrow)) (PreH6 : (borrow <= 1)) (PreH7 : ((Vn_2 - Un_2 ) = (Vsub - (borrow * U256_MOD ) ))) (PreH8 : (0 <= Ssum)) (PreH9 : (Ssum < U256_MOD)) (PreH10 : (0 <= add_carry)) (PreH11 : (add_carry <= 1)) (PreH12 : ((Rn_2 + Sn_2 ) = (Ssum + (add_carry * U256_MOD ) ))) (PreH13 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 (Vsub ÷ 2 ) R2n Ssum (unsigned_last_nbits ((k + 1 )) (64)) carry )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un_2 )
  **  (store_u256 ( &( "v" ) ) (Vsub ÷ 2 ) )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Ssum )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Un: Z)  (Vn: Z)  (Rn: Z)  (Sn: Z) ,
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn (unsigned_last_nbits ((k + 1 )) (64)) carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_17_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  (store_u256 ( &( "v" ) ) Vn )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un_2 )
  **  (store_u256 ( &( "r" ) ) Rn_2 )
  **  (store_u256 ( &( "s" ) ) Sn_2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Un: Z)  (Rn: Z)  (Sn: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn_2 k carry ) ” 
  &&  “ (k <= 512) ” 
  &&  “ (256 <= k) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= carry) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_17_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn_2 k carry )
.

Definition MontgInvModp_entail_wit_17_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  (k <= 512)
.

Definition MontgInvModp_entail_wit_17_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  (256 <= k)
.

Definition MontgInvModp_entail_wit_17_non_alias_split_goal_4 := 
forall (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  (carry <= 1)
.

Definition MontgInvModp_entail_wit_17_non_alias_split_goal_5 := 
forall (A_non_alias: Z) (Un_2: Z) (Vn: Z) (Rn_2: Z) (Sn_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vn = 0)) (PreH6 : (i = 0)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un_2 Vn Rn_2 Sn_2 k carry )) ,
  (0 <= carry)
.

Definition MontgInvModp_entail_wit_18_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  (store_u256 ( &( "v" ) ) Vi )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui_2 )
  **  (store_u256 ( &( "r" ) ) Ri_2 )
  **  (store_u256 ( &( "s" ) ) Si_2 )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Ui: Z)  (Ri: Z)  (Si: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri_2 k carry ) ” 
  &&  “ (k <= 512) ” 
  &&  “ (256 <= k) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= carry) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_18_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  (sm2p_mont_inv_phase1_exit_carry A_in_place Ri_2 k carry )
.

Definition MontgInvModp_entail_wit_18_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  (k <= 512)
.

Definition MontgInvModp_entail_wit_18_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  (256 <= k)
.

Definition MontgInvModp_entail_wit_18_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  (carry <= 1)
.

Definition MontgInvModp_entail_wit_18_in_place_split_goal_5 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui_2: Z) (Vi: Z) (Ri_2: Z) (Si_2: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (Vi = 0)) (PreH6 : (result_pre = a_pre)) (PreH7 : (i = 0)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui_2 Vi Ri_2 Si_2 k carry )) ,
  (0 <= carry)
.

Definition MontgInvModp_entail_wit_19_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry > 0)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH8 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (carry > 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (carry_2 > 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k_2 carry_2 ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k_2 carry_2 ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_19_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (Un: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry_2 > 0)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i_2 = 0)) (PreH4 : (0 <= carry_2)) (PreH5 : (carry_2 <= 1)) (PreH6 : (256 <= k_2)) (PreH7 : (k_2 <= 512)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k_2 carry_2 )) (PreH9 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k_2 carry_2 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (k: Z)  (carry: Z)  (i: Z) ,
  “ (carry > 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (carry_2 > 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k_2 carry_2 ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k_2 carry_2 ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_20_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry > 0)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH8 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (carry > 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (carry_2 > 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k_2 carry_2 ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k_2 carry_2 ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_20_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (Un: Z) (Rn: Z) (Sn: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry_2 > 0)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i_2 = 0)) (PreH4 : (0 <= carry_2)) (PreH5 : (carry_2 <= 1)) (PreH6 : (256 <= k_2)) (PreH7 : (k_2 <= 512)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k_2 carry_2 )) (PreH9 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k_2 carry_2 )) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (k: Z)  (carry: Z)  (i: Z) ,
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (carry > 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (Ri = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (carry_2 > 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k_2 carry_2 ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k_2 carry_2 ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_21_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Rn - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (carry > 0)) (PreH44 : (i = 0)) (PreH45 : (0 <= carry)) (PreH46 : (carry <= 1)) (PreH47 : (256 <= k)) (PreH48 : (k <= 512)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH50 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (store_u256 ( &( "r" ) ) S )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R1: Z) ,
  “ (i = 0) ” 
  &&  “ (0 < carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R1 k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R1 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Rn - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (carry > 0)) (PreH43 : (i = 0)) (PreH44 : (0 <= carry)) (PreH45 : (carry <= 1)) (PreH46 : (256 <= k)) (PreH47 : (k <= 512)) (PreH48 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH49 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_residue A_non_alias S k ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_21_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Rn - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (carry > 0)) (PreH43 : (i = 0)) (PreH44 : (0 <= carry)) (PreH45 : (carry <= 1)) (PreH46 : (256 <= k)) (PreH47 : (k <= 512)) (PreH48 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH49 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (sm2p_mont_inv_post_loop_residue A_non_alias S k )
.

Definition MontgInvModp_entail_wit_22_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Ri - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (carry > 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (0 <= carry)) (PreH47 : (carry <= 1)) (PreH48 : (256 <= k)) (PreH49 : (k <= 512)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH51 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (store_u256 ( &( "r" ) ) S )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R1: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R1 k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R1 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Ri - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (carry > 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (0 <= carry)) (PreH46 : (carry <= 1)) (PreH47 : (256 <= k)) (PreH48 : (k <= 512)) (PreH49 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH50 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_residue A_in_place S k ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_22_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Ri - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (carry > 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (0 <= carry)) (PreH46 : (carry <= 1)) (PreH47 : (256 <= k)) (PreH48 : (k <= 512)) (PreH49 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH50 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (sm2p_mont_inv_post_loop_residue A_in_place S k )
.

Definition MontgInvModp_entail_wit_23_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R1: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (i = 0)) (PreH2 : (0 < carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_post_loop_residue A_non_alias R1 k )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R1 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2n: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_23_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (PreH1 : (carry <= 0)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH8 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2n: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (PreH1 : (carry <= 0)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH8 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_residue A_non_alias Rn k ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_23_2_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (PreH1 : (carry <= 0)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH8 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (sm2p_mont_inv_post_loop_residue A_non_alias Rn k )
.

Definition MontgInvModp_entail_wit_24_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R1: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 < carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_post_loop_residue A_in_place R1 k )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R1 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2i: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_24_2_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry <= 0)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH9 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R2i: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry <= 0)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH9 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_residue A_in_place Ri k ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_24_2_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (PreH1 : (carry <= 0)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH9 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (sm2p_mont_inv_post_loop_residue A_in_place Ri k )
.

Definition MontgInvModp_entail_wit_25_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_25_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (R2n: Z) (R2i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (0 <= carry_2)) (PreH4 : (carry_2 <= 1)) (PreH5 : (256 <= k_2)) (PreH6 : (k_2 <= 512)) (PreH7 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (k: Z)  (carry: Z)  (i: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_26_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_26_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (R2n: Z) (R2i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (0 <= carry_2)) (PreH4 : (carry_2 <= 1)) (PreH5 : (256 <= k_2)) (PreH6 : (k_2 <= 512)) (PreH7 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 )) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (k: Z)  (carry: Z)  (i: Z) ,
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_27_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval_3 = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_27_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_27_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH6 : (x3_8 < U64_MOD)) (PreH7 : (0 <= x3_8)) (PreH8 : (x2_8 < U64_MOD)) (PreH9 : (0 <= x2_8)) (PreH10 : (x1_8 < U64_MOD)) (PreH11 : (0 <= x1_8)) (PreH12 : (x0_8 < U64_MOD)) (PreH13 : (0 <= x0_8)) (PreH14 : (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH15 : (x3_7 < U64_MOD)) (PreH16 : (0 <= x3_7)) (PreH17 : (x2_7 < U64_MOD)) (PreH18 : (0 <= x2_7)) (PreH19 : (x1_7 < U64_MOD)) (PreH20 : (0 <= x1_7)) (PreH21 : (x0_7 < U64_MOD)) (PreH22 : (0 <= x0_7)) (PreH23 : (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH24 : (x3_6 < U64_MOD)) (PreH25 : (0 <= x3_6)) (PreH26 : (x2_6 < U64_MOD)) (PreH27 : (0 <= x2_6)) (PreH28 : (x1_6 < U64_MOD)) (PreH29 : (0 <= x1_6)) (PreH30 : (x0_6 < U64_MOD)) (PreH31 : (0 <= x0_6)) (PreH32 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH33 : (x3_5 < U64_MOD)) (PreH34 : (0 <= x3_5)) (PreH35 : (x2_5 < U64_MOD)) (PreH36 : (0 <= x2_5)) (PreH37 : (x1_5 < U64_MOD)) (PreH38 : (0 <= x1_5)) (PreH39 : (x0_5 < U64_MOD)) (PreH40 : (0 <= x0_5)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval_3 = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_27_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH6 : (x3_8 < U64_MOD)) (PreH7 : (0 <= x3_8)) (PreH8 : (x2_8 < U64_MOD)) (PreH9 : (0 <= x2_8)) (PreH10 : (x1_8 < U64_MOD)) (PreH11 : (0 <= x1_8)) (PreH12 : (x0_8 < U64_MOD)) (PreH13 : (0 <= x0_8)) (PreH14 : (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH15 : (x3_7 < U64_MOD)) (PreH16 : (0 <= x3_7)) (PreH17 : (x2_7 < U64_MOD)) (PreH18 : (0 <= x2_7)) (PreH19 : (x1_7 < U64_MOD)) (PreH20 : (0 <= x1_7)) (PreH21 : (x0_7 < U64_MOD)) (PreH22 : (0 <= x0_7)) (PreH23 : (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH24 : (x3_6 < U64_MOD)) (PreH25 : (0 <= x3_6)) (PreH26 : (x2_6 < U64_MOD)) (PreH27 : (0 <= x2_6)) (PreH28 : (x1_6 < U64_MOD)) (PreH29 : (0 <= x1_6)) (PreH30 : (x0_6 < U64_MOD)) (PreH31 : (0 <= x0_6)) (PreH32 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH33 : (x3_5 < U64_MOD)) (PreH34 : (0 <= x3_5)) (PreH35 : (x2_5 < U64_MOD)) (PreH36 : (0 <= x2_5)) (PreH37 : (x1_5 < U64_MOD)) (PreH38 : (0 <= x1_5)) (PreH39 : (x0_5 < U64_MOD)) (PreH40 : (0 <= x0_5)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_28_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_28_2_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval_3 <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_28_3_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH6 : (x3_8 < U64_MOD)) (PreH7 : (0 <= x3_8)) (PreH8 : (x2_8 < U64_MOD)) (PreH9 : (0 <= x2_8)) (PreH10 : (x1_8 < U64_MOD)) (PreH11 : (0 <= x1_8)) (PreH12 : (x0_8 < U64_MOD)) (PreH13 : (0 <= x0_8)) (PreH14 : (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH15 : (x3_7 < U64_MOD)) (PreH16 : (0 <= x3_7)) (PreH17 : (x2_7 < U64_MOD)) (PreH18 : (0 <= x2_7)) (PreH19 : (x1_7 < U64_MOD)) (PreH20 : (0 <= x1_7)) (PreH21 : (x0_7 < U64_MOD)) (PreH22 : (0 <= x0_7)) (PreH23 : (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH24 : (x3_6 < U64_MOD)) (PreH25 : (0 <= x3_6)) (PreH26 : (x2_6 < U64_MOD)) (PreH27 : (0 <= x2_6)) (PreH28 : (x1_6 < U64_MOD)) (PreH29 : (0 <= x1_6)) (PreH30 : (x0_6 < U64_MOD)) (PreH31 : (0 <= x0_6)) (PreH32 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH33 : (x3_5 < U64_MOD)) (PreH34 : (0 <= x3_5)) (PreH35 : (x2_5 < U64_MOD)) (PreH36 : (0 <= x2_5)) (PreH37 : (x1_5 < U64_MOD)) (PreH38 : (0 <= x1_5)) (PreH39 : (x0_5 < U64_MOD)) (PreH40 : (0 <= x0_5)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval_2 <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_28_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH6 : (x3_8 < U64_MOD)) (PreH7 : (0 <= x3_8)) (PreH8 : (x2_8 < U64_MOD)) (PreH9 : (0 <= x2_8)) (PreH10 : (x1_8 < U64_MOD)) (PreH11 : (0 <= x1_8)) (PreH12 : (x0_8 < U64_MOD)) (PreH13 : (0 <= x0_8)) (PreH14 : (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH15 : (x3_7 < U64_MOD)) (PreH16 : (0 <= x3_7)) (PreH17 : (x2_7 < U64_MOD)) (PreH18 : (0 <= x2_7)) (PreH19 : (x1_7 < U64_MOD)) (PreH20 : (0 <= x1_7)) (PreH21 : (x0_7 < U64_MOD)) (PreH22 : (0 <= x0_7)) (PreH23 : (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH24 : (x3_6 < U64_MOD)) (PreH25 : (0 <= x3_6)) (PreH26 : (x2_6 < U64_MOD)) (PreH27 : (0 <= x2_6)) (PreH28 : (x1_6 < U64_MOD)) (PreH29 : (0 <= x1_6)) (PreH30 : (x0_6 < U64_MOD)) (PreH31 : (0 <= x0_6)) (PreH32 : (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH33 : (x3_5 < U64_MOD)) (PreH34 : (0 <= x3_5)) (PreH35 : (x2_5 < U64_MOD)) (PreH36 : (0 <= x2_5)) (PreH37 : (x1_5 < U64_MOD)) (PreH38 : (0 <= x1_5)) (PreH39 : (x0_5 < U64_MOD)) (PreH40 : (0 <= x0_5)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval_3 <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R2i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_29_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_12: Z)  (x2_12: Z)  (x1_12: Z)  (x0_12: Z)  (x3_11: Z)  (x2_11: Z)  (x1_11: Z)  (x0_11: Z)  (retval_2: Z)  (x3_10: Z)  (x2_10: Z)  (x1_10: Z)  (x0_10: Z)  (x3_9: Z)  (x2_9: Z)  (x1_9: Z)  (x0_9: Z)  (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ ((u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) = (u256_of_limbs (x0_12) (x1_12) (x2_12) (x3_12))) ” 
  &&  “ (x3_12 < U64_MOD) ” 
  &&  “ (0 <= x3_12) ” 
  &&  “ (x2_12 < U64_MOD) ” 
  &&  “ (0 <= x2_12) ” 
  &&  “ (x1_12 < U64_MOD) ” 
  &&  “ (0 <= x1_12) ” 
  &&  “ (x0_12 < U64_MOD) ” 
  &&  “ (0 <= x0_12) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_11) (x1_11) (x2_11) (x3_11))) ” 
  &&  “ (x3_11 < U64_MOD) ” 
  &&  “ (0 <= x3_11) ” 
  &&  “ (x2_11 < U64_MOD) ” 
  &&  “ (0 <= x2_11) ” 
  &&  “ (x1_11 < U64_MOD) ” 
  &&  “ (0 <= x1_11) ” 
  &&  “ (x0_11 < U64_MOD) ” 
  &&  “ (0 <= x0_11) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_10) (x1_10) (x2_10) (x3_10))) ” 
  &&  “ (x3_10 < U64_MOD) ” 
  &&  “ (0 <= x3_10) ” 
  &&  “ (x2_10 < U64_MOD) ” 
  &&  “ (0 <= x2_10) ” 
  &&  “ (x1_10 < U64_MOD) ” 
  &&  “ (0 <= x1_10) ” 
  &&  “ (x0_10 < U64_MOD) ” 
  &&  “ (0 <= x0_10) ” 
  &&  “ (0 = (u256_of_limbs (x0_9) (x1_9) (x2_9) (x3_9))) ” 
  &&  “ (x3_9 < U64_MOD) ” 
  &&  “ (0 <= x3_9) ” 
  &&  “ (x2_9 < U64_MOD) ” 
  &&  “ (0 <= x2_9) ” 
  &&  “ (x1_9 < U64_MOD) ” 
  &&  “ (0 <= x1_9) ” 
  &&  “ (x0_9 < U64_MOD) ” 
  &&  “ (0 <= x0_9) ” 
  &&  “ (R2i = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Si = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_12)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_12)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_12)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_12)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_11)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_11)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_11)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_11)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_10)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_9)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_29_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (R2n: Z) (R2i: Z) (x0_7: Z) (x1_7: Z) (x2_7: Z) (x3_7: Z) (x0_8: Z) (x1_8: Z) (x2_8: Z) (x3_8: Z) (x0_9: Z) (x1_9: Z) (x2_9: Z) (x3_9: Z) (x0_10: Z) (x1_10: Z) (x2_10: Z) (x3_10: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_10) (x1_10) (x2_10) (x3_10)))) (PreH6 : (x3_10 < U64_MOD)) (PreH7 : (0 <= x3_10)) (PreH8 : (x2_10 < U64_MOD)) (PreH9 : (0 <= x2_10)) (PreH10 : (x1_10 < U64_MOD)) (PreH11 : (0 <= x1_10)) (PreH12 : (x0_10 < U64_MOD)) (PreH13 : (0 <= x0_10)) (PreH14 : (0 = (u256_of_limbs (x0_9) (x1_9) (x2_9) (x3_9)))) (PreH15 : (x3_9 < U64_MOD)) (PreH16 : (0 <= x3_9)) (PreH17 : (x2_9 < U64_MOD)) (PreH18 : (0 <= x2_9)) (PreH19 : (x1_9 < U64_MOD)) (PreH20 : (0 <= x1_9)) (PreH21 : (x0_9 < U64_MOD)) (PreH22 : (0 <= x0_9)) (PreH23 : (R2i = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)))) (PreH24 : (x3_8 < U64_MOD)) (PreH25 : (0 <= x3_8)) (PreH26 : (x2_8 < U64_MOD)) (PreH27 : (0 <= x2_8)) (PreH28 : (x1_8 < U64_MOD)) (PreH29 : (0 <= x1_8)) (PreH30 : (x0_8 < U64_MOD)) (PreH31 : (0 <= x0_8)) (PreH32 : (Si = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7)))) (PreH33 : (x3_7 < U64_MOD)) (PreH34 : (0 <= x3_7)) (PreH35 : (x2_7 < U64_MOD)) (PreH36 : (0 <= x2_7)) (PreH37 : (x1_7 < U64_MOD)) (PreH38 : (0 <= x1_7)) (PreH39 : (x0_7 < U64_MOD)) (PreH40 : (0 <= x0_7)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i_2 = 0)) (PreH43 : (0 <= carry_2)) (PreH44 : (carry_2 <= 1)) (PreH45 : (256 <= k_2)) (PreH46 : (k_2 <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 )) (PreH48 : (retval_2 <> 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_10)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_9)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (retval: Z)  (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (k: Z)  (carry: Z)  (i: Z) ,
  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_12: Z)  (x2_12: Z)  (x1_12: Z)  (x0_12: Z)  (x3_11: Z)  (x2_11: Z)  (x1_11: Z)  (x0_11: Z) ,
  “ ((u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) = (u256_of_limbs (x0_12) (x1_12) (x2_12) (x3_12))) ” 
  &&  “ (x3_12 < U64_MOD) ” 
  &&  “ (0 <= x3_12) ” 
  &&  “ (x2_12 < U64_MOD) ” 
  &&  “ (0 <= x2_12) ” 
  &&  “ (x1_12 < U64_MOD) ” 
  &&  “ (0 <= x1_12) ” 
  &&  “ (x0_12 < U64_MOD) ” 
  &&  “ (0 <= x0_12) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_11) (x1_11) (x2_11) (x3_11))) ” 
  &&  “ (x3_11 < U64_MOD) ” 
  &&  “ (0 <= x3_11) ” 
  &&  “ (x2_11 < U64_MOD) ” 
  &&  “ (0 <= x2_11) ” 
  &&  “ (x1_11 < U64_MOD) ” 
  &&  “ (0 <= x1_11) ” 
  &&  “ (x0_11 < U64_MOD) ” 
  &&  “ (0 <= x0_11) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_10) (x1_10) (x2_10) (x3_10))) ” 
  &&  “ (x3_10 < U64_MOD) ” 
  &&  “ (0 <= x3_10) ” 
  &&  “ (x2_10 < U64_MOD) ” 
  &&  “ (0 <= x2_10) ” 
  &&  “ (x1_10 < U64_MOD) ” 
  &&  “ (0 <= x1_10) ” 
  &&  “ (x0_10 < U64_MOD) ” 
  &&  “ (0 <= x0_10) ” 
  &&  “ (0 = (u256_of_limbs (x0_9) (x1_9) (x2_9) (x3_9))) ” 
  &&  “ (x3_9 < U64_MOD) ” 
  &&  “ (0 <= x3_9) ” 
  &&  “ (x2_9 < U64_MOD) ” 
  &&  “ (0 <= x2_9) ” 
  &&  “ (x1_9 < U64_MOD) ” 
  &&  “ (0 <= x1_9) ” 
  &&  “ (x0_9 < U64_MOD) ” 
  &&  “ (0 <= x0_9) ” 
  &&  “ (R2i = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (Si = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k_2 ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_12)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_12)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_12)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_12)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_11)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_11)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_11)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_11)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_10)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_10)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_9)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_9)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_30_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((R2n - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH8 : (x3_6 < U64_MOD)) (PreH9 : (0 <= x3_6)) (PreH10 : (x2_6 < U64_MOD)) (PreH11 : (0 <= x2_6)) (PreH12 : (x1_6 < U64_MOD)) (PreH13 : (0 <= x1_6)) (PreH14 : (x0_6 < U64_MOD)) (PreH15 : (0 <= x0_6)) (PreH16 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH17 : (x3_5 < U64_MOD)) (PreH18 : (0 <= x3_5)) (PreH19 : (x2_5 < U64_MOD)) (PreH20 : (0 <= x2_5)) (PreH21 : (x1_5 < U64_MOD)) (PreH22 : (0 <= x1_5)) (PreH23 : (x0_5 < U64_MOD)) (PreH24 : (0 <= x0_5)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 1)) (PreH28 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH29 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH30 : (x3_4 < U64_MOD)) (PreH31 : (0 <= x3_4)) (PreH32 : (x2_4 < U64_MOD)) (PreH33 : (0 <= x2_4)) (PreH34 : (x1_4 < U64_MOD)) (PreH35 : (0 <= x1_4)) (PreH36 : (x0_4 < U64_MOD)) (PreH37 : (0 <= x0_4)) (PreH38 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH39 : (x3_3 < U64_MOD)) (PreH40 : (0 <= x3_3)) (PreH41 : (x2_3 < U64_MOD)) (PreH42 : (0 <= x2_3)) (PreH43 : (x1_3 < U64_MOD)) (PreH44 : (0 <= x1_3)) (PreH45 : (x0_3 < U64_MOD)) (PreH46 : (0 <= x0_3)) (PreH47 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH48 : (x3_2 < U64_MOD)) (PreH49 : (0 <= x3_2)) (PreH50 : (x2_2 < U64_MOD)) (PreH51 : (0 <= x2_2)) (PreH52 : (x1_2 < U64_MOD)) (PreH53 : (0 <= x1_2)) (PreH54 : (x0_2 < U64_MOD)) (PreH55 : (0 <= x0_2)) (PreH56 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH57 : (x3 < U64_MOD)) (PreH58 : (0 <= x3)) (PreH59 : (x2 < U64_MOD)) (PreH60 : (0 <= x2)) (PreH61 : (x1 < U64_MOD)) (PreH62 : (0 <= x1)) (PreH63 : (x0 < U64_MOD)) (PreH64 : (0 <= x0)) (PreH65 : (i = 0)) (PreH66 : (0 <= carry)) (PreH67 : (carry <= 1)) (PreH68 : (256 <= k)) (PreH69 : (k <= 512)) (PreH70 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH71 : (retval <> 0)) ,
  (store_u256 ( &( "r" ) ) S )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R3: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R3 k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R3 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((R2n - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH7 : (x3_6 < U64_MOD)) (PreH8 : (0 <= x3_6)) (PreH9 : (x2_6 < U64_MOD)) (PreH10 : (0 <= x2_6)) (PreH11 : (x1_6 < U64_MOD)) (PreH12 : (0 <= x1_6)) (PreH13 : (x0_6 < U64_MOD)) (PreH14 : (0 <= x0_6)) (PreH15 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH16 : (x3_5 < U64_MOD)) (PreH17 : (0 <= x3_5)) (PreH18 : (x2_5 < U64_MOD)) (PreH19 : (0 <= x2_5)) (PreH20 : (x1_5 < U64_MOD)) (PreH21 : (0 <= x1_5)) (PreH22 : (x0_5 < U64_MOD)) (PreH23 : (0 <= x0_5)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (retval = 1)) (PreH27 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH28 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH29 : (x3_4 < U64_MOD)) (PreH30 : (0 <= x3_4)) (PreH31 : (x2_4 < U64_MOD)) (PreH32 : (0 <= x2_4)) (PreH33 : (x1_4 < U64_MOD)) (PreH34 : (0 <= x1_4)) (PreH35 : (x0_4 < U64_MOD)) (PreH36 : (0 <= x0_4)) (PreH37 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH38 : (x3_3 < U64_MOD)) (PreH39 : (0 <= x3_3)) (PreH40 : (x2_3 < U64_MOD)) (PreH41 : (0 <= x2_3)) (PreH42 : (x1_3 < U64_MOD)) (PreH43 : (0 <= x1_3)) (PreH44 : (x0_3 < U64_MOD)) (PreH45 : (0 <= x0_3)) (PreH46 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (i = 0)) (PreH65 : (0 <= carry)) (PreH66 : (carry <= 1)) (PreH67 : (256 <= k)) (PreH68 : (k <= 512)) (PreH69 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH70 : (retval <> 0)) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_norm A_non_alias S k ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_30_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((R2n - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH7 : (x3_6 < U64_MOD)) (PreH8 : (0 <= x3_6)) (PreH9 : (x2_6 < U64_MOD)) (PreH10 : (0 <= x2_6)) (PreH11 : (x1_6 < U64_MOD)) (PreH12 : (0 <= x1_6)) (PreH13 : (x0_6 < U64_MOD)) (PreH14 : (0 <= x0_6)) (PreH15 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH16 : (x3_5 < U64_MOD)) (PreH17 : (0 <= x3_5)) (PreH18 : (x2_5 < U64_MOD)) (PreH19 : (0 <= x2_5)) (PreH20 : (x1_5 < U64_MOD)) (PreH21 : (0 <= x1_5)) (PreH22 : (x0_5 < U64_MOD)) (PreH23 : (0 <= x0_5)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (retval = 1)) (PreH27 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH28 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH29 : (x3_4 < U64_MOD)) (PreH30 : (0 <= x3_4)) (PreH31 : (x2_4 < U64_MOD)) (PreH32 : (0 <= x2_4)) (PreH33 : (x1_4 < U64_MOD)) (PreH34 : (0 <= x1_4)) (PreH35 : (x0_4 < U64_MOD)) (PreH36 : (0 <= x0_4)) (PreH37 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH38 : (x3_3 < U64_MOD)) (PreH39 : (0 <= x3_3)) (PreH40 : (x2_3 < U64_MOD)) (PreH41 : (0 <= x2_3)) (PreH42 : (x1_3 < U64_MOD)) (PreH43 : (0 <= x1_3)) (PreH44 : (x0_3 < U64_MOD)) (PreH45 : (0 <= x0_3)) (PreH46 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (i = 0)) (PreH65 : (0 <= carry)) (PreH66 : (carry <= 1)) (PreH67 : (256 <= k)) (PreH68 : (k <= 512)) (PreH69 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH70 : (retval <> 0)) ,
  (sm2p_mont_inv_post_loop_norm A_non_alias S k )
.

Definition MontgInvModp_entail_wit_31_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((R2i - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH8 : (x3_6 < U64_MOD)) (PreH9 : (0 <= x3_6)) (PreH10 : (x2_6 < U64_MOD)) (PreH11 : (0 <= x2_6)) (PreH12 : (x1_6 < U64_MOD)) (PreH13 : (0 <= x1_6)) (PreH14 : (x0_6 < U64_MOD)) (PreH15 : (0 <= x0_6)) (PreH16 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH17 : (x3_5 < U64_MOD)) (PreH18 : (0 <= x3_5)) (PreH19 : (x2_5 < U64_MOD)) (PreH20 : (0 <= x2_5)) (PreH21 : (x1_5 < U64_MOD)) (PreH22 : (0 <= x1_5)) (PreH23 : (x0_5 < U64_MOD)) (PreH24 : (0 <= x0_5)) (PreH25 : (0 <= retval)) (PreH26 : (retval <= 1)) (PreH27 : (retval = 1)) (PreH28 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH29 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH30 : (x3_4 < U64_MOD)) (PreH31 : (0 <= x3_4)) (PreH32 : (x2_4 < U64_MOD)) (PreH33 : (0 <= x2_4)) (PreH34 : (x1_4 < U64_MOD)) (PreH35 : (0 <= x1_4)) (PreH36 : (x0_4 < U64_MOD)) (PreH37 : (0 <= x0_4)) (PreH38 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH39 : (x3_3 < U64_MOD)) (PreH40 : (0 <= x3_3)) (PreH41 : (x2_3 < U64_MOD)) (PreH42 : (0 <= x2_3)) (PreH43 : (x1_3 < U64_MOD)) (PreH44 : (0 <= x1_3)) (PreH45 : (x0_3 < U64_MOD)) (PreH46 : (0 <= x0_3)) (PreH47 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH48 : (x3_2 < U64_MOD)) (PreH49 : (0 <= x3_2)) (PreH50 : (x2_2 < U64_MOD)) (PreH51 : (0 <= x2_2)) (PreH52 : (x1_2 < U64_MOD)) (PreH53 : (0 <= x1_2)) (PreH54 : (x0_2 < U64_MOD)) (PreH55 : (0 <= x0_2)) (PreH56 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH57 : (x3 < U64_MOD)) (PreH58 : (0 <= x3)) (PreH59 : (x2 < U64_MOD)) (PreH60 : (0 <= x2)) (PreH61 : (x1 < U64_MOD)) (PreH62 : (0 <= x1)) (PreH63 : (x0 < U64_MOD)) (PreH64 : (0 <= x0)) (PreH65 : (result_pre = a_pre)) (PreH66 : (i = 0)) (PreH67 : (0 <= carry)) (PreH68 : (carry <= 1)) (PreH69 : (256 <= k)) (PreH70 : (k <= 512)) (PreH71 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH72 : (retval <> 0)) ,
  (store_u256 ( &( "r" ) ) S )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R3: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R3 k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R3 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((R2i - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH7 : (x3_6 < U64_MOD)) (PreH8 : (0 <= x3_6)) (PreH9 : (x2_6 < U64_MOD)) (PreH10 : (0 <= x2_6)) (PreH11 : (x1_6 < U64_MOD)) (PreH12 : (0 <= x1_6)) (PreH13 : (x0_6 < U64_MOD)) (PreH14 : (0 <= x0_6)) (PreH15 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH16 : (x3_5 < U64_MOD)) (PreH17 : (0 <= x3_5)) (PreH18 : (x2_5 < U64_MOD)) (PreH19 : (0 <= x2_5)) (PreH20 : (x1_5 < U64_MOD)) (PreH21 : (0 <= x1_5)) (PreH22 : (x0_5 < U64_MOD)) (PreH23 : (0 <= x0_5)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (retval = 1)) (PreH27 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH28 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH29 : (x3_4 < U64_MOD)) (PreH30 : (0 <= x3_4)) (PreH31 : (x2_4 < U64_MOD)) (PreH32 : (0 <= x2_4)) (PreH33 : (x1_4 < U64_MOD)) (PreH34 : (0 <= x1_4)) (PreH35 : (x0_4 < U64_MOD)) (PreH36 : (0 <= x0_4)) (PreH37 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH38 : (x3_3 < U64_MOD)) (PreH39 : (0 <= x3_3)) (PreH40 : (x2_3 < U64_MOD)) (PreH41 : (0 <= x2_3)) (PreH42 : (x1_3 < U64_MOD)) (PreH43 : (0 <= x1_3)) (PreH44 : (x0_3 < U64_MOD)) (PreH45 : (0 <= x0_3)) (PreH46 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (result_pre = a_pre)) (PreH65 : (i = 0)) (PreH66 : (0 <= carry)) (PreH67 : (carry <= 1)) (PreH68 : (256 <= k)) (PreH69 : (k <= 512)) (PreH70 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH71 : (retval <> 0)) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_norm A_in_place S k ) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_31_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((R2i - SM2_P_Z ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH7 : (x3_6 < U64_MOD)) (PreH8 : (0 <= x3_6)) (PreH9 : (x2_6 < U64_MOD)) (PreH10 : (0 <= x2_6)) (PreH11 : (x1_6 < U64_MOD)) (PreH12 : (0 <= x1_6)) (PreH13 : (x0_6 < U64_MOD)) (PreH14 : (0 <= x0_6)) (PreH15 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH16 : (x3_5 < U64_MOD)) (PreH17 : (0 <= x3_5)) (PreH18 : (x2_5 < U64_MOD)) (PreH19 : (0 <= x2_5)) (PreH20 : (x1_5 < U64_MOD)) (PreH21 : (0 <= x1_5)) (PreH22 : (x0_5 < U64_MOD)) (PreH23 : (0 <= x0_5)) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (retval = 1)) (PreH27 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH28 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH29 : (x3_4 < U64_MOD)) (PreH30 : (0 <= x3_4)) (PreH31 : (x2_4 < U64_MOD)) (PreH32 : (0 <= x2_4)) (PreH33 : (x1_4 < U64_MOD)) (PreH34 : (0 <= x1_4)) (PreH35 : (x0_4 < U64_MOD)) (PreH36 : (0 <= x0_4)) (PreH37 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH38 : (x3_3 < U64_MOD)) (PreH39 : (0 <= x3_3)) (PreH40 : (x2_3 < U64_MOD)) (PreH41 : (0 <= x2_3)) (PreH42 : (x1_3 < U64_MOD)) (PreH43 : (0 <= x1_3)) (PreH44 : (x0_3 < U64_MOD)) (PreH45 : (0 <= x0_3)) (PreH46 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH47 : (x3_2 < U64_MOD)) (PreH48 : (0 <= x3_2)) (PreH49 : (x2_2 < U64_MOD)) (PreH50 : (0 <= x2_2)) (PreH51 : (x1_2 < U64_MOD)) (PreH52 : (0 <= x1_2)) (PreH53 : (x0_2 < U64_MOD)) (PreH54 : (0 <= x0_2)) (PreH55 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH56 : (x3 < U64_MOD)) (PreH57 : (0 <= x3)) (PreH58 : (x2 < U64_MOD)) (PreH59 : (0 <= x2)) (PreH60 : (x1 < U64_MOD)) (PreH61 : (0 <= x1)) (PreH62 : (x0 < U64_MOD)) (PreH63 : (0 <= x0)) (PreH64 : (result_pre = a_pre)) (PreH65 : (i = 0)) (PreH66 : (0 <= carry)) (PreH67 : (carry <= 1)) (PreH68 : (256 <= k)) (PreH69 : (k <= 512)) (PreH70 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH71 : (retval <> 0)) ,
  (sm2p_mont_inv_post_loop_norm A_in_place S k )
.

Definition MontgInvModp_entail_wit_32_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R3: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_post_loop_norm A_non_alias R3 k )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R3 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R4n: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_32_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R4n: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval = 0)) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_norm A_non_alias R2n k ) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_32_2_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval = 0)) ,
  (sm2p_mont_inv_post_loop_norm A_non_alias R2n k )
.

Definition MontgInvModp_entail_wit_32_2_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (i = 0)) (PreH42 : (0 <= carry)) (PreH43 : (carry <= 1)) (PreH44 : (256 <= k)) (PreH45 : (k <= 512)) (PreH46 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH47 : (retval = 0)) ,
  ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z)
.

Definition MontgInvModp_entail_wit_33_1_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R3: Z) (i: Z) (carry: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (sm2p_mont_inv_post_loop_norm A_in_place R3 k )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R3 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R4i: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_33_2_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval = 0)) ,
  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R4i: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval = 0)) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_post_loop_norm A_in_place R2i k ) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_33_2_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval = 0)) ,
  (sm2p_mont_inv_post_loop_norm A_in_place R2i k )
.

Definition MontgInvModp_entail_wit_33_2_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH5 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH6 : (x3_4 < U64_MOD)) (PreH7 : (0 <= x3_4)) (PreH8 : (x2_4 < U64_MOD)) (PreH9 : (0 <= x2_4)) (PreH10 : (x1_4 < U64_MOD)) (PreH11 : (0 <= x1_4)) (PreH12 : (x0_4 < U64_MOD)) (PreH13 : (0 <= x0_4)) (PreH14 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH15 : (x3_3 < U64_MOD)) (PreH16 : (0 <= x3_3)) (PreH17 : (x2_3 < U64_MOD)) (PreH18 : (0 <= x2_3)) (PreH19 : (x1_3 < U64_MOD)) (PreH20 : (0 <= x1_3)) (PreH21 : (x0_3 < U64_MOD)) (PreH22 : (0 <= x0_3)) (PreH23 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH24 : (x3_2 < U64_MOD)) (PreH25 : (0 <= x3_2)) (PreH26 : (x2_2 < U64_MOD)) (PreH27 : (0 <= x2_2)) (PreH28 : (x1_2 < U64_MOD)) (PreH29 : (0 <= x1_2)) (PreH30 : (x0_2 < U64_MOD)) (PreH31 : (0 <= x0_2)) (PreH32 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH33 : (x3 < U64_MOD)) (PreH34 : (0 <= x3)) (PreH35 : (x2 < U64_MOD)) (PreH36 : (0 <= x2)) (PreH37 : (x1 < U64_MOD)) (PreH38 : (0 <= x1)) (PreH39 : (x0 < U64_MOD)) (PreH40 : (0 <= x0)) (PreH41 : (result_pre = a_pre)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH48 : (retval = 0)) ,
  ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z)
.

Definition MontgInvModp_entail_wit_34_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (R4i: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (“ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k_2 ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_34_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (R4n: Z) (R4i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (0 <= carry_2)) (PreH4 : (carry_2 <= 1)) (PreH5 : (256 <= k_2)) (PreH6 : (k_2 <= 512)) (PreH7 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k_2 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (k: Z)  (carry: Z)  (i: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (“ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k_2 ) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_35_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (R4i: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= k)) (PreH5 : (k <= 512)) (PreH6 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z)  (k_2: Z)  (carry_2: Z)  (i_2: Z) ,
  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R4i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k_2 ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_35_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Un: Z) (Sn: Z) (Ui: Z) (Si: Z) (i_2: Z) (carry_2: Z) (k_2: Z) (R4n: Z) (R4i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i_2 = 0)) (PreH3 : (0 <= carry_2)) (PreH4 : (carry_2 <= 1)) (PreH5 : (256 <= k_2)) (PreH6 : (k_2 <= 512)) (PreH7 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k_2 )) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  (EX (x3_4: Z)  (x2_4: Z)  (x1_4: Z)  (x0_4: Z)  (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (k: Z)  (carry: Z)  (i: Z) ,
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
  ||
  (EX (x3_8: Z)  (x2_8: Z)  (x1_8: Z)  (x0_8: Z)  (x3_7: Z)  (x2_7: Z)  (x1_7: Z)  (x0_7: Z)  (x3_6: Z)  (x2_6: Z)  (x1_6: Z)  (x0_6: Z)  (x3_5: Z)  (x2_5: Z)  (x1_5: Z)  (x0_5: Z) ,
  “ (Ui = (u256_of_limbs (x0_8) (x1_8) (x2_8) (x3_8))) ” 
  &&  “ (x3_8 < U64_MOD) ” 
  &&  “ (0 <= x3_8) ” 
  &&  “ (x2_8 < U64_MOD) ” 
  &&  “ (0 <= x2_8) ” 
  &&  “ (x1_8 < U64_MOD) ” 
  &&  “ (0 <= x1_8) ” 
  &&  “ (x0_8 < U64_MOD) ” 
  &&  “ (0 <= x0_8) ” 
  &&  “ (0 = (u256_of_limbs (x0_7) (x1_7) (x2_7) (x3_7))) ” 
  &&  “ (x3_7 < U64_MOD) ” 
  &&  “ (0 <= x3_7) ” 
  &&  “ (x2_7 < U64_MOD) ” 
  &&  “ (0 <= x2_7) ” 
  &&  “ (x1_7 < U64_MOD) ” 
  &&  “ (0 <= x1_7) ” 
  &&  “ (x0_7 < U64_MOD) ” 
  &&  “ (0 <= x0_7) ” 
  &&  “ (R4i = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ (Si = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i_2 = 0) ” 
  &&  “ (0 <= carry_2) ” 
  &&  “ (carry_2 <= 1) ” 
  &&  “ (256 <= k_2) ” 
  &&  “ (k_2 <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k_2 ) ”
  &&  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_8)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_8)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_7)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_7)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i_2)
  **  ((( &( "carry" ) )) # UChar  |-> carry_2)
  **  ((( &( "k" ) )) # UInt64  |-> k_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop ))
.

Definition MontgInvModp_entail_wit_36_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4n ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (i = 0)) (PreH44 : (0 <= carry)) (PreH45 : (carry <= 1)) (PreH46 : (256 <= k)) (PreH47 : (k <= 512)) (PreH48 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (store_u256 ( &( "r" ) ) S )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R5n: Z) ,
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4n ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_result A_non_alias S k ) ” 
  &&  “ (S < SM2_P_Z) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_36_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4n ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (sm2p_mont_inv_phase1_result A_non_alias S k )
.

Definition MontgInvModp_entail_wit_36_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4n ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (i = 0)) (PreH43 : (0 <= carry)) (PreH44 : (carry <= 1)) (PreH45 : (256 <= k)) (PreH46 : (k <= 512)) (PreH47 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (S < SM2_P_Z)
.

Definition MontgInvModp_entail_wit_37_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4i ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (0 <= carry)) (PreH46 : (carry <= 1)) (PreH47 : (256 <= k)) (PreH48 : (k <= 512)) (PreH49 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (store_u256 ( &( "r" ) ) S )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (R5i: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4i ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (result_pre = a_pre)) (PreH43 : (i = 0)) (PreH44 : (0 <= carry)) (PreH45 : (carry <= 1)) (PreH46 : (256 <= k)) (PreH47 : (k <= 512)) (PreH48 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  TT && emp 
|--
  “ (sm2p_mont_inv_phase1_result A_in_place S k ) ” 
  &&  “ (S < SM2_P_Z) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_37_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4i ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (result_pre = a_pre)) (PreH43 : (i = 0)) (PreH44 : (0 <= carry)) (PreH45 : (carry <= 1)) (PreH46 : (256 <= k)) (PreH47 : (k <= 512)) (PreH48 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (sm2p_mont_inv_phase1_result A_in_place S k )
.

Definition MontgInvModp_entail_wit_37_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((SM2_P_Z - R4i ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH7 : (x3_4 < U64_MOD)) (PreH8 : (0 <= x3_4)) (PreH9 : (x2_4 < U64_MOD)) (PreH10 : (0 <= x2_4)) (PreH11 : (x1_4 < U64_MOD)) (PreH12 : (0 <= x1_4)) (PreH13 : (x0_4 < U64_MOD)) (PreH14 : (0 <= x0_4)) (PreH15 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH16 : (x3_3 < U64_MOD)) (PreH17 : (0 <= x3_3)) (PreH18 : (x2_3 < U64_MOD)) (PreH19 : (0 <= x2_3)) (PreH20 : (x1_3 < U64_MOD)) (PreH21 : (0 <= x1_3)) (PreH22 : (x0_3 < U64_MOD)) (PreH23 : (0 <= x0_3)) (PreH24 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH25 : (x3_2 < U64_MOD)) (PreH26 : (0 <= x3_2)) (PreH27 : (x2_2 < U64_MOD)) (PreH28 : (0 <= x2_2)) (PreH29 : (x1_2 < U64_MOD)) (PreH30 : (0 <= x1_2)) (PreH31 : (x0_2 < U64_MOD)) (PreH32 : (0 <= x0_2)) (PreH33 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH34 : (x3 < U64_MOD)) (PreH35 : (0 <= x3)) (PreH36 : (x2 < U64_MOD)) (PreH37 : (0 <= x2)) (PreH38 : (x1 < U64_MOD)) (PreH39 : (0 <= x1)) (PreH40 : (x0 < U64_MOD)) (PreH41 : (0 <= x0)) (PreH42 : (result_pre = a_pre)) (PreH43 : (i = 0)) (PreH44 : (0 <= carry)) (PreH45 : (carry <= 1)) (PreH46 : (256 <= k)) (PreH47 : (k <= 512)) (PreH48 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (S < SM2_P_Z)
.

Definition MontgInvModp_entail_wit_38_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R5n: Z) (PreH1 : (k <> 256)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (0 <= R5n)) (PreH8 : (R5n < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n k )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (k <> 256) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n k ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_39_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R5i: Z) (PreH1 : (k <> 256)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i k )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (k <> 256) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i k ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_40_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= (((2 * 256 ) - K0n ) ÷ 64 )) ” 
  &&  “ ((((2 * 256 ) - K0n ) ÷ 64 ) < 4) ” 
  &&  “ (0 <= (((2 * 256 ) - K0n ) % ( 64 ) )) ” 
  &&  “ ((((2 * 256 ) - K0n ) % ( 64 ) ) < 64) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n K0n ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0n (((2 * 256 ) - K0n ) ÷ 64 ) (((2 * 256 ) - K0n ) % ( 64 ) ) ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  “ (sm2p_mont_inv_phase2_index K0n (((2 * 256 ) - K0n ) ÷ 64 ) (((2 * 256 ) - K0n ) % ( 64 ) ) ) ” 
  &&  “ ((((2 * 256 ) - K0n ) % ( 64 ) ) < 64) ” 
  &&  “ (0 <= (((2 * 256 ) - K0n ) % ( 64 ) )) ” 
  &&  “ ((((2 * 256 ) - K0n ) ÷ 64 ) < 4) ” 
  &&  “ (0 <= (((2 * 256 ) - K0n ) ÷ 64 )) ”
  &&  (UndefStructPredu32 result_pre )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
).

Definition MontgInvModp_entail_wit_40_non_alias_split_goal_1 := 
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  “ (sm2p_mont_inv_phase2_index K0n (((2 * 256 ) - K0n ) ÷ 64 ) (((2 * 256 ) - K0n ) % ( 64 ) ) ) ”
.

Definition MontgInvModp_entail_wit_40_non_alias_split_goal_2 := 
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  “ ((((2 * 256 ) - K0n ) % ( 64 ) ) < 64) ”
.

Definition MontgInvModp_entail_wit_40_non_alias_split_goal_3 := 
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 <= (((2 * 256 ) - K0n ) % ( 64 ) )) ”
.

Definition MontgInvModp_entail_wit_40_non_alias_split_goal_4 := 
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  “ ((((2 * 256 ) - K0n ) ÷ 64 ) < 4) ”
.

Definition MontgInvModp_entail_wit_40_non_alias_split_goal_5 := 
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  “ (0 <= (((2 * 256 ) - K0n ) ÷ 64 )) ”
.

Definition MontgInvModp_entail_wit_40_non_alias_split_goal_spatial := 
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0n)) (PreH6 : (K0n <= 512)) (PreH7 : (K0n <> 256)) (PreH8 : (0 <= R5n)) (PreH9 : (R5n < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (UndefStructPredu32 result_pre )
|--
  (UndefStructPredu32 result_pre )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
.

Definition MontgInvModp_entail_wit_41_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= (((2 * 256 ) - K0i ) ÷ 64 )) ” 
  &&  “ ((((2 * 256 ) - K0i ) ÷ 64 ) < 4) ” 
  &&  “ (0 <= (((2 * 256 ) - K0i ) % ( 64 ) )) ” 
  &&  “ ((((2 * 256 ) - K0i ) % ( 64 ) ) < 64) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i K0i ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0i (((2 * 256 ) - K0i ) ÷ 64 ) (((2 * 256 ) - K0i ) % ( 64 ) ) ) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  “ (sm2p_mont_inv_phase2_index K0i (((2 * 256 ) - K0i ) ÷ 64 ) (((2 * 256 ) - K0i ) % ( 64 ) ) ) ” 
  &&  “ ((((2 * 256 ) - K0i ) % ( 64 ) ) < 64) ” 
  &&  “ (0 <= (((2 * 256 ) - K0i ) % ( 64 ) )) ” 
  &&  “ ((((2 * 256 ) - K0i ) ÷ 64 ) < 4) ” 
  &&  “ (0 <= (((2 * 256 ) - K0i ) ÷ 64 )) ”
  &&  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
).

Definition MontgInvModp_entail_wit_41_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  “ (sm2p_mont_inv_phase2_index K0i (((2 * 256 ) - K0i ) ÷ 64 ) (((2 * 256 ) - K0i ) % ( 64 ) ) ) ”
.

Definition MontgInvModp_entail_wit_41_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  “ ((((2 * 256 ) - K0i ) % ( 64 ) ) < 64) ”
.

Definition MontgInvModp_entail_wit_41_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  “ (0 <= (((2 * 256 ) - K0i ) % ( 64 ) )) ”
.

Definition MontgInvModp_entail_wit_41_in_place_split_goal_4 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  “ ((((2 * 256 ) - K0i ) ÷ 64 ) < 4) ”
.

Definition MontgInvModp_entail_wit_41_in_place_split_goal_5 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  “ (0 <= (((2 * 256 ) - K0i ) ÷ 64 )) ”
.

Definition MontgInvModp_entail_wit_41_in_place_split_goal_spatial := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (retval: Z) (PreH1 : (retval = ( &( "t" ) ))) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= K0i)) (PreH7 : (K0i <= 512)) (PreH8 : (K0i <> 256)) (PreH9 : (0 <= R5i)) (PreH10 : (R5i < SM2_P_Z)) (PreH11 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_u256 ( &( "t" ) ) 0 )
|--
  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
.

Definition MontgInvModp_entail_wit_42_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (replace_Znth (i) ((unsigned_last_nbits ((Z.shiftl 1 k)) (64))) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
|--
  EX (Tn: Z) ,
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (0 <= Tn) ” 
  &&  “ (Tn < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n K0n ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0n i k ) ” 
  &&  “ (Tn = (Z.pow (2) ((512 - K0n )))) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "t" ) ) Tn )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  TT && emp 
|--
  “ ((Z.pow (2) ((512 - K0n ))) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.pow (2) ((512 - K0n )))) ” 
  &&  “ ((u64_list_value ((replace_Znth (i) ((unsigned_last_nbits ((Z.shiftl 1 k)) (64))) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) = (Z.pow (2) ((512 - K0n )))) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_42_non_alias_split_goal_1 := 
forall (A_non_alias: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  ((Z.pow (2) ((512 - K0n ))) < SM2_P_Z)
.

Definition MontgInvModp_entail_wit_42_non_alias_split_goal_2 := 
forall (A_non_alias: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  (0 <= (Z.pow (2) ((512 - K0n ))))
.

Definition MontgInvModp_entail_wit_42_non_alias_split_goal_3 := 
forall (A_non_alias: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  ((u64_list_value ((replace_Znth (i) ((unsigned_last_nbits ((Z.shiftl 1 k)) (64))) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) = (Z.pow (2) ((512 - K0n ))))
.

Definition MontgInvModp_entail_wit_43_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (replace_Znth (i) ((unsigned_last_nbits ((Z.shiftl 1 k)) (64))) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))) )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
|--
  EX (Ti: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (0 <= Ti) ” 
  &&  “ (Ti < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i K0i ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0i i k ) ” 
  &&  “ (Ti = (Z.pow (2) ((512 - K0i )))) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "t" ) ) Ti )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  TT && emp 
|--
  “ ((Z.pow (2) ((512 - K0i ))) < SM2_P_Z) ” 
  &&  “ (0 <= (Z.pow (2) ((512 - K0i )))) ” 
  &&  “ ((u64_list_value ((replace_Znth (i) ((unsigned_last_nbits ((Z.shiftl 1 k)) (64))) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) = (Z.pow (2) ((512 - K0i )))) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_43_in_place_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  ((Z.pow (2) ((512 - K0i ))) < SM2_P_Z)
.

Definition MontgInvModp_entail_wit_43_in_place_split_goal_2 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  (0 <= (Z.pow (2) ((512 - K0i ))))
.

Definition MontgInvModp_entail_wit_43_in_place_split_goal_3 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  ((u64_list_value ((replace_Znth (i) ((unsigned_last_nbits ((Z.shiftl 1 k)) (64))) ((cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))))))) = (Z.pow (2) ((512 - K0i ))))
.

Definition MontgInvModp_entail_wit_44_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (Tn: Z) (K: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_P_Z)) (PreH3 : ((R * U256_MOD ) = ((R5n * Tn ) + (K * SM2_P_Z ) ))) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= k)) (PreH9 : (k < 64)) (PreH10 : (0 <= Tn)) (PreH11 : (Tn < SM2_P_Z)) (PreH12 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH13 : (sm2p_mont_inv_phase2_index K0n i k )) (PreH14 : (Tn = (Z.pow (2) ((512 - K0n ))))) ,
  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "t" ) ) Tn )
  **  (store_fp result_pre R )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Sn )
|--
  EX (Kout: Z)  (Kmul: Z)  (Out: Z) ,
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (0 <= Out) ” 
  &&  “ (Out < SM2_P_Z) ” 
  &&  “ ((Out * U256_MOD ) = ((R5n * Tn ) + (Kmul * SM2_P_Z ) )) ” 
  &&  “ ((A_non_alias * Out ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "t" ) ) Tn )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (Tn: Z) (K: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_P_Z)) (PreH3 : ((R * U256_MOD ) = ((R5n * Tn ) + (K * SM2_P_Z ) ))) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (0 <= i)) (PreH7 : (i < 4)) (PreH8 : (0 <= k)) (PreH9 : (k < 64)) (PreH10 : (0 <= Tn)) (PreH11 : (Tn < SM2_P_Z)) (PreH12 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH13 : (sm2p_mont_inv_phase2_index K0n i k )) (PreH14 : (Tn = (Z.pow (2) ((512 - K0n ))))) ,
  TT && emp 
|--
  EX (Kout: Z)  (Kmul: Z) ,
  “ ((R * U256_MOD ) = ((R5n * (Z.pow (2) ((512 - K0n ))) ) + (Kmul * SM2_P_Z ) )) ” 
  &&  “ ((A_non_alias * R ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_45_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (Ti: Z) (K: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_P_Z)) (PreH3 : ((R * U256_MOD ) = ((R5i * Ti ) + (K * SM2_P_Z ) ))) (PreH4 : (result_pre = a_pre)) (PreH5 : (0 <= carry)) (PreH6 : (carry <= 1)) (PreH7 : (0 <= i)) (PreH8 : (i < 4)) (PreH9 : (0 <= k)) (PreH10 : (k < 64)) (PreH11 : (0 <= Ti)) (PreH12 : (Ti < SM2_P_Z)) (PreH13 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH14 : (sm2p_mont_inv_phase2_index K0i i k )) (PreH15 : (Ti = (Z.pow (2) ((512 - K0i ))))) ,
  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "t" ) ) Ti )
  **  (store_fp result_pre R )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Si )
|--
  EX (Kout: Z)  (Kmul: Z)  (Out: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (0 <= Out) ” 
  &&  “ (Out < SM2_P_Z) ” 
  &&  “ ((Out * U256_MOD ) = ((R5i * Ti ) + (Kmul * SM2_P_Z ) )) ” 
  &&  “ ((A_in_place * Out ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "t" ) ) Ti )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (Ti: Z) (K: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_P_Z)) (PreH3 : ((R * U256_MOD ) = ((R5i * Ti ) + (K * SM2_P_Z ) ))) (PreH4 : (result_pre = a_pre)) (PreH5 : (0 <= carry)) (PreH6 : (carry <= 1)) (PreH7 : (0 <= i)) (PreH8 : (i < 4)) (PreH9 : (0 <= k)) (PreH10 : (k < 64)) (PreH11 : (0 <= Ti)) (PreH12 : (Ti < SM2_P_Z)) (PreH13 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH14 : (sm2p_mont_inv_phase2_index K0i i k )) (PreH15 : (Ti = (Z.pow (2) ((512 - K0i ))))) ,
  TT && emp 
|--
  EX (Kout: Z)  (Kmul: Z) ,
  “ ((R * U256_MOD ) = ((R5i * (Z.pow (2) ((512 - K0i ))) ) + (Kmul * SM2_P_Z ) )) ” 
  &&  “ ((A_in_place * R ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_46_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R5n: Z) (PreH1 : (k = 256)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= k)) (PreH6 : (k <= 512)) (PreH7 : (0 <= R5n)) (PreH8 : (R5n < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n k )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (k = 256) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n 256 ) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_entail_wit_47_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R5i: Z) (PreH1 : (k = 256)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i k )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i 256 ) ”
  &&  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (R5i: Z) (PreH1 : (k = 256)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i k )) ,
  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
|--
  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
).

Definition MontgInvModp_entail_wit_47_in_place_split_goal_spatial := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (R5i: Z) (PreH1 : (k = 256)) (PreH2 : (result_pre = a_pre)) (PreH3 : (i = 0)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (256 <= k)) (PreH7 : (k <= 512)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i k )) ,
  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
|--
  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
.

Definition MontgInvModp_entail_wit_48_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval = result_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5n)) (PreH7 : (R5n < SM2_P_Z)) (PreH8 : (sm2p_mont_inv_phase1_result A_non_alias R5n 256 )) ,
  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 result_pre R5n )
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Kout: Z) ,
  “ (k = 256) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ ((A_non_alias * R5n ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre R5n )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (A_non_alias: Z) (R5n: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval = result_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5n)) (PreH7 : (R5n < SM2_P_Z)) (PreH8 : (sm2p_mont_inv_phase1_result A_non_alias R5n 256 )) ,
  TT && emp 
|--
  EX (Kout: Z) ,
  “ ((A_non_alias * R5n ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_49_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval = result_pre)) (PreH2 : (result_pre = a_pre)) (PreH3 : (k = 256)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (i = 0)) (PreH7 : (0 <= R5i)) (PreH8 : (R5i < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_in_place R5i 256 )) ,
  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 result_pre R5i )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Kout: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ ((A_in_place * R5i ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp result_pre R5i )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (R5i: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (PreH1 : (retval = result_pre)) (PreH2 : (result_pre = a_pre)) (PreH3 : (k = 256)) (PreH4 : (0 <= carry)) (PreH5 : (carry <= 1)) (PreH6 : (i = 0)) (PreH7 : (0 <= R5i)) (PreH8 : (R5i < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_in_place R5i 256 )) ,
  TT && emp 
|--
  EX (Kout: Z) ,
  “ ((A_in_place * R5i ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  emp
).

Definition MontgInvModp_entail_wit_50_1_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (Tn: Z) (Out_2: Z) (Kmul: Z) (Kout_2: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (0 <= Out_2)) (PreH8 : (Out_2 < SM2_P_Z)) (PreH9 : ((Out_2 * U256_MOD ) = ((R5n * Tn ) + (Kmul * SM2_P_Z ) ))) (PreH10 : ((A_non_alias * Out_2 ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Out_2 )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "t" ) ) Tn )
  **  (store_sm2_rhop )
|--
  EX (Kout: Z)  (Out: Z) ,
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= Out) ” 
  &&  “ (Out < SM2_P_Z) ” 
  &&  “ ((A_non_alias * Out ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (Tn: Z) (Out_2: Z) (Kmul: Z) (Kout_2: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (0 <= Out_2)) (PreH8 : (Out_2 < SM2_P_Z)) (PreH9 : ((Out_2 * U256_MOD ) = ((R5n * Tn ) + (Kmul * SM2_P_Z ) ))) (PreH10 : ((A_non_alias * Out_2 ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "t" ) ) Tn )
|--
  EX (Kout: Z) ,
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= Out_2) ” 
  &&  “ (Out_2 < SM2_P_Z) ” 
  &&  “ ((A_non_alias * Out_2 ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
).

Definition MontgInvModp_entail_wit_50_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (Kout_2: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (k = 256)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (i = 0)) (PreH5 : (0 <= R5n)) (PreH6 : (R5n < SM2_P_Z)) (PreH7 : ((A_non_alias * R5n ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre R5n )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Kout: Z)  (Out: Z) ,
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= Out) ” 
  &&  “ (Out < SM2_P_Z) ” 
  &&  “ ((A_non_alias * Out ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (Kout_2: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (k = 256)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (i = 0)) (PreH5 : (0 <= R5n)) (PreH6 : (R5n < SM2_P_Z)) (PreH7 : ((A_non_alias * R5n ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
|--
  EX (Kout: Z) ,
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ ((A_non_alias * R5n ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
).

Definition MontgInvModp_entail_wit_51_1_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (Ti: Z) (Out_2: Z) (Kmul: Z) (Kout_2: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (0 <= Out_2)) (PreH9 : (Out_2 < SM2_P_Z)) (PreH10 : ((Out_2 * U256_MOD ) = ((R5i * Ti ) + (Kmul * SM2_P_Z ) ))) (PreH11 : ((A_in_place * Out_2 ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_fp result_pre Out_2 )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "t" ) ) Ti )
  **  (store_sm2_rhop )
|--
  EX (Kout: Z)  (Out: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= Out) ” 
  &&  “ (Out < SM2_P_Z) ” 
  &&  “ ((A_in_place * Out ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (Ti: Z) (Out_2: Z) (Kmul: Z) (Kout_2: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (0 <= Out_2)) (PreH9 : (Out_2 < SM2_P_Z)) (PreH10 : ((Out_2 * U256_MOD ) = ((R5i * Ti ) + (Kmul * SM2_P_Z ) ))) (PreH11 : ((A_in_place * Out_2 ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "t" ) ) Ti )
|--
  EX (Kout: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= Out_2) ” 
  &&  “ (Out_2 < SM2_P_Z) ” 
  &&  “ ((A_in_place * Out_2 ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
).

Definition MontgInvModp_entail_wit_51_2_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (Kout_2: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5i)) (PreH7 : (R5i < SM2_P_Z)) (PreH8 : ((A_in_place * R5i ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_fp result_pre R5i )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  EX (Kout: Z)  (Out: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= Out) ” 
  &&  “ (Out < SM2_P_Z) ” 
  &&  “ ((A_in_place * Out ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (Kout_2: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5i)) (PreH7 : (R5i < SM2_P_Z)) (PreH8 : ((A_in_place * R5i ) = (U256_MOD + (Kout_2 * SM2_P_Z ) ))) ,
  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
|--
  EX (Kout: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= 256) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ ((A_in_place * R5i ) = (U256_MOD + (Kout * SM2_P_Z ) )) ”
  &&  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
).

Definition MontgInvModp_return_wit_1_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Out: Z) (Kout: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k <= 256)) (PreH7 : (0 <= Out)) (PreH8 : (Out < SM2_P_Z)) (PreH9 : ((A_non_alias * Out ) = (U256_MOD + (Kout * SM2_P_Z ) ))) ,
  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Z: Z) ,
  “ (0 <= Z) ” 
  &&  “ (Z < SM2_P_Z) ” 
  &&  “ ((A_non_alias * Z ) = (U256_MOD + (K * SM2_P_Z ) )) ”
  &&  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Out: Z) (Kout: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k <= 256)) (PreH7 : (0 <= Out)) (PreH8 : (Out < SM2_P_Z)) (PreH9 : ((A_non_alias * Out ) = (U256_MOD + (Kout * SM2_P_Z ) ))) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ ((A_non_alias * Out ) = (U256_MOD + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition MontgInvModp_return_wit_2_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Out: Z) (Kout: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k <= 256)) (PreH8 : (0 <= Out)) (PreH9 : (Out < SM2_P_Z)) (PreH10 : ((A_in_place * Out ) = (U256_MOD + (Kout * SM2_P_Z ) ))) ,
  (store_fp result_pre Out )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Z: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Z) ” 
  &&  “ (Z < SM2_P_Z) ” 
  &&  “ ((A_in_place * Z ) = (U256_MOD + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Out: Z) (Kout: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k <= 256)) (PreH8 : (0 <= Out)) (PreH9 : (Out < SM2_P_Z)) (PreH10 : ((A_in_place * Out ) = (U256_MOD + (Kout * SM2_P_Z ) ))) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ ((A_in_place * Out ) = (U256_MOD + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition MontgInvModp_partial_solve_wit_1_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (A_non_alias <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ”
).

Definition MontgInvModp_partial_solve_wit_1_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (A_non_alias <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ”
.

Definition MontgInvModp_partial_solve_wit_1_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) ,
  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_1_non_alias := MontgInvModp_partial_solve_wit_1_non_alias_pure -> MontgInvModp_partial_solve_wit_1_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_2_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (result_pre = a_pre)) (PreH4 : (A_in_place <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ”
).

Definition MontgInvModp_partial_solve_wit_2_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (0 <= UINT64_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (result_pre = a_pre)) (PreH4 : (A_in_place <> 0)) ,
  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ”
.

Definition MontgInvModp_partial_solve_wit_2_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (A_in_place <> 0)) ,
  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "u" ) ) )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_2_in_place := MontgInvModp_partial_solve_wit_2_in_place_pure -> MontgInvModp_partial_solve_wit_2_in_place_aux.

Definition MontgInvModp_partial_solve_wit_3_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "u" ) ))) (PreH2 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH3 : (A_non_alias <> 0)) ,
  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_3_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (PreH1 : (retval = ( &( "u" ) ))) (PreH2 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH3 : (A_non_alias <> 0)) ,
  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_3_non_alias := MontgInvModp_partial_solve_wit_3_non_alias_pure -> MontgInvModp_partial_solve_wit_3_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_4_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (PreH1 : (retval = ( &( "u" ) ))) (PreH2 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH3 : (result_pre = a_pre)) (PreH4 : (A_in_place <> 0)) ,
  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_4_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (PreH1 : (retval = ( &( "u" ) ))) (PreH2 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH3 : (result_pre = a_pre)) (PreH4 : (A_in_place <> 0)) ,
  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "v" ) ) )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_4_in_place := MontgInvModp_partial_solve_wit_4_in_place_pure -> MontgInvModp_partial_solve_wit_4_in_place_aux.

Definition MontgInvModp_partial_solve_wit_5_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (A_non_alias <> 0)) ,
  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_5_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (A_non_alias <> 0)) ,
  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ” 
  &&  “ (retval_2 = ( &( "v" ) )) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (UndefStructPredu32 ( &( "r" ) ) )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_5_non_alias := MontgInvModp_partial_solve_wit_5_non_alias_pure -> MontgInvModp_partial_solve_wit_5_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_6_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (result_pre = a_pre)) (PreH5 : (A_in_place <> 0)) ,
  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_6_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = ( &( "v" ) ))) (PreH2 : (retval = ( &( "u" ) ))) (PreH3 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH4 : (result_pre = a_pre)) (PreH5 : (A_in_place <> 0)) ,
  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UndefStructPredu32 ( &( "r" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ” 
  &&  “ (retval_2 = ( &( "v" ) )) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (UndefStructPredu32 ( &( "r" ) ) )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_6_in_place := MontgInvModp_partial_solve_wit_6_in_place_pure -> MontgInvModp_partial_solve_wit_6_in_place_aux.

Definition MontgInvModp_partial_solve_wit_7_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (A_non_alias <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_7_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (A_non_alias <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ” 
  &&  “ (retval_3 = ( &( "r" ) )) ” 
  &&  “ (retval_2 = ( &( "v" ) )) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (A_non_alias <> 0) ”
  &&  (UndefStructPredu32 ( &( "s" ) ) )
  **  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "v" ) ) A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_7_non_alias := MontgInvModp_partial_solve_wit_7_non_alias_pure -> MontgInvModp_partial_solve_wit_7_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_8_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (result_pre = a_pre)) (PreH6 : (A_in_place <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  ((( &( "carry" ) )) # UChar  |-> 0)
  **  ((( &( "i" ) )) # UInt64  |-> 0)
  **  ((( &( "k" ) )) # UInt64  |-> 0)
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_8_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = ( &( "r" ) ))) (PreH2 : (retval_2 = ( &( "v" ) ))) (PreH3 : (retval = ( &( "u" ) ))) (PreH4 : ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v"))) (PreH5 : (result_pre = a_pre)) (PreH6 : (A_in_place <> 0)) ,
  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (UndefStructPredu32 ( &( "s" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ” 
  &&  “ (retval_3 = ( &( "r" ) )) ” 
  &&  “ (retval_2 = ( &( "v" ) )) ” 
  &&  “ (retval = ( &( "u" ) )) ” 
  &&  “ ((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64))) = &(( &( "SM2_P" ) )->ₛ "v")) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (UndefStructPredu32 ( &( "s" ) ) )
  **  (store_u256 ( &( "r" ) ) 0 )
  **  (store_fp a_pre A_in_place )
  **  (store_u256 ( &( "v" ) ) A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) SM2_P_Z )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_8_in_place := MontgInvModp_partial_solve_wit_8_in_place_pure -> MontgInvModp_partial_solve_wit_8_in_place_aux.

Definition MontgInvModp_partial_solve_wit_9_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (i = 0)) (PreH2 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (store_u256 ( &( "v" ) ) Vn )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_10_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ”
  &&  (store_u256 ( &( "v" ) ) Vi )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_11_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) = 0)) (PreH2 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vi <> 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_3 1) = 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_12_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) = 0)) (PreH2 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vn <> 0)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_3 1) = 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_13_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) = 0)) (PreH2 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vi <> 0)) (PreH43 : (result_pre = a_pre)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_u256 ( &( "u" ) ) ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ÷ 2 ) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_3 1) = 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ”
  &&  (store_u256 ( &( "s" ) ) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "u" ) ) ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ÷ 2 ) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_14_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_3 1) = 0)) (PreH2 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH3 : (x3_4 < U64_MOD)) (PreH4 : (0 <= x3_4)) (PreH5 : (x2_4 < U64_MOD)) (PreH6 : (0 <= x2_4)) (PreH7 : (x1_4 < U64_MOD)) (PreH8 : (0 <= x1_4)) (PreH9 : (x0_4 < U64_MOD)) (PreH10 : (0 <= x0_4)) (PreH11 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH12 : (x3_3 < U64_MOD)) (PreH13 : (0 <= x3_3)) (PreH14 : (x2_3 < U64_MOD)) (PreH15 : (0 <= x2_3)) (PreH16 : (x1_3 < U64_MOD)) (PreH17 : (0 <= x1_3)) (PreH18 : (x0_3 < U64_MOD)) (PreH19 : (0 <= x0_3)) (PreH20 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH21 : (x3_2 < U64_MOD)) (PreH22 : (0 <= x3_2)) (PreH23 : (x2_2 < U64_MOD)) (PreH24 : (0 <= x2_2)) (PreH25 : (x1_2 < U64_MOD)) (PreH26 : (0 <= x1_2)) (PreH27 : (x0_2 < U64_MOD)) (PreH28 : (0 <= x0_2)) (PreH29 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH30 : (x3 < U64_MOD)) (PreH31 : (0 <= x3)) (PreH32 : (x2 < U64_MOD)) (PreH33 : (0 <= x2)) (PreH34 : (x1 < U64_MOD)) (PreH35 : (0 <= x1)) (PreH36 : (x0 < U64_MOD)) (PreH37 : (0 <= x0)) (PreH38 : (retval = 0)) (PreH39 : (0 <= retval)) (PreH40 : (retval <= 1)) (PreH41 : (retval = 0)) (PreH42 : (Vn <> 0)) (PreH43 : (i = 0)) (PreH44 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "u" ) ) ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ÷ 2 ) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_3 1) = 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (store_u256 ( &( "s" ) ) (u256_of_limbs (x0) (x1) (x2) (x3)) )
  **  (store_u256 ( &( "u" ) ) ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) ÷ 2 ) )
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_15_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_4 1) = 0)) (PreH2 : ((Z.land x0_3 1) <> 0)) (PreH3 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vn <> 0)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_4 1) = 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_16_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_4 1) = 0)) (PreH2 : ((Z.land x0_3 1) <> 0)) (PreH3 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vi <> 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_4 1) = 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ”
  &&  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_17_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_4 1) = 0)) (PreH2 : ((Z.land x0_3 1) <> 0)) (PreH3 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vn <> 0)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (store_u256 ( &( "v" ) ) ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ÷ 2 ) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_4 1) = 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "v" ) ) ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ÷ 2 ) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_18_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_4 1) = 0)) (PreH2 : ((Z.land x0_3 1) <> 0)) (PreH3 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vi <> 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (store_u256 ( &( "v" ) ) ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ÷ 2 ) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_4 1) = 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "v" ) ) ((u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) ÷ 2 ) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_19_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_4 1) <> 0)) (PreH2 : ((Z.land x0_3 1) <> 0)) (PreH3 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vn <> 0)) (PreH44 : (i = 0)) (PreH45 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_20_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : ((Z.land x0_4 1) <> 0)) (PreH2 : ((Z.land x0_3 1) <> 0)) (PreH3 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH4 : (x3_4 < U64_MOD)) (PreH5 : (0 <= x3_4)) (PreH6 : (x2_4 < U64_MOD)) (PreH7 : (0 <= x2_4)) (PreH8 : (x1_4 < U64_MOD)) (PreH9 : (0 <= x1_4)) (PreH10 : (x0_4 < U64_MOD)) (PreH11 : (0 <= x0_4)) (PreH12 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH13 : (x3_3 < U64_MOD)) (PreH14 : (0 <= x3_3)) (PreH15 : (x2_3 < U64_MOD)) (PreH16 : (0 <= x2_3)) (PreH17 : (x1_3 < U64_MOD)) (PreH18 : (0 <= x1_3)) (PreH19 : (x0_3 < U64_MOD)) (PreH20 : (0 <= x0_3)) (PreH21 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH22 : (x3_2 < U64_MOD)) (PreH23 : (0 <= x3_2)) (PreH24 : (x2_2 < U64_MOD)) (PreH25 : (0 <= x2_2)) (PreH26 : (x1_2 < U64_MOD)) (PreH27 : (0 <= x1_2)) (PreH28 : (x0_2 < U64_MOD)) (PreH29 : (0 <= x0_2)) (PreH30 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH31 : (x3 < U64_MOD)) (PreH32 : (0 <= x3)) (PreH33 : (x2 < U64_MOD)) (PreH34 : (0 <= x2)) (PreH35 : (x1 < U64_MOD)) (PreH36 : (0 <= x1)) (PreH37 : (x0 < U64_MOD)) (PreH38 : (0 <= x0)) (PreH39 : (retval = 0)) (PreH40 : (0 <= retval)) (PreH41 : (retval <= 1)) (PreH42 : (retval = 0)) (PreH43 : (Vi <> 0)) (PreH44 : (result_pre = a_pre)) (PreH45 : (i = 0)) (PreH46 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) ,
  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ”
  &&  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_21_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "u" ) ) = ( &( "u" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_21_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "u" ) ) = ( &( "u" ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_21_non_alias := MontgInvModp_partial_solve_wit_21_non_alias_pure -> MontgInvModp_partial_solve_wit_21_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_22_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "u" ) ) = ( &( "u" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_22_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "u" ) ) = ( &( "u" ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_22_in_place := MontgInvModp_partial_solve_wit_22_in_place_pure -> MontgInvModp_partial_solve_wit_22_in_place_aux.

Definition MontgInvModp_partial_solve_wit_23_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Un - Vn ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "u" ) ) = ( &( "u" ) ))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH11 : ((Z.land x0_4 1) <> 0)) (PreH12 : ((Z.land x0_3 1) <> 0)) (PreH13 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH14 : (x3_4 < U64_MOD)) (PreH15 : (0 <= x3_4)) (PreH16 : (x2_4 < U64_MOD)) (PreH17 : (0 <= x2_4)) (PreH18 : (x1_4 < U64_MOD)) (PreH19 : (0 <= x1_4)) (PreH20 : (x0_4 < U64_MOD)) (PreH21 : (0 <= x0_4)) (PreH22 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH23 : (x3_3 < U64_MOD)) (PreH24 : (0 <= x3_3)) (PreH25 : (x2_3 < U64_MOD)) (PreH26 : (0 <= x2_3)) (PreH27 : (x1_3 < U64_MOD)) (PreH28 : (0 <= x1_3)) (PreH29 : (x0_3 < U64_MOD)) (PreH30 : (0 <= x0_3)) (PreH31 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (retval = 0)) (PreH50 : (0 <= retval)) (PreH51 : (retval <= 1)) (PreH52 : (retval = 0)) (PreH53 : (Vn <> 0)) (PreH54 : (i = 0)) (PreH55 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH56 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) S )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Un - Vn ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) S )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_24_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Ui - Vi ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "u" ) ) = ( &( "u" ) ))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH11 : ((Z.land x0_4 1) <> 0)) (PreH12 : ((Z.land x0_3 1) <> 0)) (PreH13 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH14 : (x3_4 < U64_MOD)) (PreH15 : (0 <= x3_4)) (PreH16 : (x2_4 < U64_MOD)) (PreH17 : (0 <= x2_4)) (PreH18 : (x1_4 < U64_MOD)) (PreH19 : (0 <= x1_4)) (PreH20 : (x0_4 < U64_MOD)) (PreH21 : (0 <= x0_4)) (PreH22 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH23 : (x3_3 < U64_MOD)) (PreH24 : (0 <= x3_3)) (PreH25 : (x2_3 < U64_MOD)) (PreH26 : (0 <= x2_3)) (PreH27 : (x1_3 < U64_MOD)) (PreH28 : (0 <= x1_3)) (PreH29 : (x0_3 < U64_MOD)) (PreH30 : (0 <= x0_3)) (PreH31 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (retval = 0)) (PreH50 : (0 <= retval)) (PreH51 : (retval <= 1)) (PreH52 : (retval = 0)) (PreH53 : (Vi <> 0)) (PreH54 : (result_pre = a_pre)) (PreH55 : (i = 0)) (PreH56 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH57 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) S )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Ui - Vi ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "u" ) ) S )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_25_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Un - Vn ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 1)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vn <> 0)) (PreH53 : (i = 0)) (PreH54 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH55 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_25_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Un - Vn ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 1)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vn <> 0)) (PreH53 : (i = 0)) (PreH54 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH55 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Un - Vn ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_25_non_alias := MontgInvModp_partial_solve_wit_25_non_alias_pure -> MontgInvModp_partial_solve_wit_25_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_26_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Ui - Vi ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 1)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vi <> 0)) (PreH53 : (result_pre = a_pre)) (PreH54 : (i = 0)) (PreH55 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH56 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_26_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Ui - Vi ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 1)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vi <> 0)) (PreH53 : (result_pre = a_pre)) (PreH54 : (i = 0)) (PreH55 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH56 : (retval_2 <> 0)) ,
  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Ui - Vi ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_26_in_place := MontgInvModp_partial_solve_wit_26_in_place_pure -> MontgInvModp_partial_solve_wit_26_in_place_aux.

Definition MontgInvModp_partial_solve_wit_27_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (S_2: Z) (retval_3: Z) (PreH1 : (0 <= S_2)) (PreH2 : (S_2 < U256_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((Rn + Sn ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow)) (PreH10 : (borrow <= 1)) (PreH11 : ((Un - Vn ) = (S - (borrow * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vn <> 0)) (PreH59 : (i = 0)) (PreH60 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH61 : (retval_2 <> 0)) ,
  (store_u256 ( &( "r" ) ) S_2 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S_2) ” 
  &&  “ (S_2 < U256_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((Rn + Sn ) = (S_2 + (retval_3 * U256_MOD ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Un - Vn ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "r" ) ) S_2 )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vn )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_28_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (S_2: Z) (retval_3: Z) (PreH1 : (0 <= S_2)) (PreH2 : (S_2 < U256_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((Ri + Si ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH6 : (( &( "r" ) ) = ( &( "r" ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow)) (PreH10 : (borrow <= 1)) (PreH11 : ((Ui - Vi ) = (S - (borrow * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vi <> 0)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH62 : (retval_2 <> 0)) ,
  (store_u256 ( &( "r" ) ) S_2 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S_2) ” 
  &&  “ (S_2 < U256_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((Ri + Si ) = (S_2 + (retval_3 * U256_MOD ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Ui - Vi ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) > (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "r" ) ) S_2 )
  **  (store_u256 ( &( "u" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "v" ) ) Vi )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_29_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "v" ) ) = ( &( "v" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_29_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vn <> 0)) (PreH48 : (i = 0)) (PreH49 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH50 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "v" ) ) = ( &( "v" ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "v" ) ) Vn )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_29_non_alias := MontgInvModp_partial_solve_wit_29_non_alias_pure -> MontgInvModp_partial_solve_wit_29_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_30_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "v" ) ) = ( &( "v" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_30_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH5 : ((Z.land x0_4 1) <> 0)) (PreH6 : ((Z.land x0_3 1) <> 0)) (PreH7 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH8 : (x3_4 < U64_MOD)) (PreH9 : (0 <= x3_4)) (PreH10 : (x2_4 < U64_MOD)) (PreH11 : (0 <= x2_4)) (PreH12 : (x1_4 < U64_MOD)) (PreH13 : (0 <= x1_4)) (PreH14 : (x0_4 < U64_MOD)) (PreH15 : (0 <= x0_4)) (PreH16 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH17 : (x3_3 < U64_MOD)) (PreH18 : (0 <= x3_3)) (PreH19 : (x2_3 < U64_MOD)) (PreH20 : (0 <= x2_3)) (PreH21 : (x1_3 < U64_MOD)) (PreH22 : (0 <= x1_3)) (PreH23 : (x0_3 < U64_MOD)) (PreH24 : (0 <= x0_3)) (PreH25 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH26 : (x3_2 < U64_MOD)) (PreH27 : (0 <= x3_2)) (PreH28 : (x2_2 < U64_MOD)) (PreH29 : (0 <= x2_2)) (PreH30 : (x1_2 < U64_MOD)) (PreH31 : (0 <= x1_2)) (PreH32 : (x0_2 < U64_MOD)) (PreH33 : (0 <= x0_2)) (PreH34 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH35 : (x3 < U64_MOD)) (PreH36 : (0 <= x3)) (PreH37 : (x2 < U64_MOD)) (PreH38 : (0 <= x2)) (PreH39 : (x1 < U64_MOD)) (PreH40 : (0 <= x1)) (PreH41 : (x0 < U64_MOD)) (PreH42 : (0 <= x0)) (PreH43 : (retval = 0)) (PreH44 : (0 <= retval)) (PreH45 : (retval <= 1)) (PreH46 : (retval = 0)) (PreH47 : (Vi <> 0)) (PreH48 : (result_pre = a_pre)) (PreH49 : (i = 0)) (PreH50 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH51 : (retval_2 = 0)) ,
  (store_u256 ( &( "u" ) ) (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) )
  **  (store_u256 ( &( "v" ) ) (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)) )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "v" ) ) = ( &( "v" ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "v" ) ) Vi )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_30_in_place := MontgInvModp_partial_solve_wit_30_in_place_pure -> MontgInvModp_partial_solve_wit_30_in_place_aux.

Definition MontgInvModp_partial_solve_wit_31_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Vn - Un ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "v" ) ) = ( &( "v" ) ))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH11 : ((Z.land x0_4 1) <> 0)) (PreH12 : ((Z.land x0_3 1) <> 0)) (PreH13 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH14 : (x3_4 < U64_MOD)) (PreH15 : (0 <= x3_4)) (PreH16 : (x2_4 < U64_MOD)) (PreH17 : (0 <= x2_4)) (PreH18 : (x1_4 < U64_MOD)) (PreH19 : (0 <= x1_4)) (PreH20 : (x0_4 < U64_MOD)) (PreH21 : (0 <= x0_4)) (PreH22 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH23 : (x3_3 < U64_MOD)) (PreH24 : (0 <= x3_3)) (PreH25 : (x2_3 < U64_MOD)) (PreH26 : (0 <= x2_3)) (PreH27 : (x1_3 < U64_MOD)) (PreH28 : (0 <= x1_3)) (PreH29 : (x0_3 < U64_MOD)) (PreH30 : (0 <= x0_3)) (PreH31 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (retval = 0)) (PreH50 : (0 <= retval)) (PreH51 : (retval <= 1)) (PreH52 : (retval = 0)) (PreH53 : (Vn <> 0)) (PreH54 : (i = 0)) (PreH55 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH56 : (retval_2 = 0)) ,
  (store_u256 ( &( "v" ) ) S )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vn - Un ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "v" ) ) S )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_32_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Vi - Ui ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (( &( "v" ) ) = ( &( "v" ) ))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH11 : ((Z.land x0_4 1) <> 0)) (PreH12 : ((Z.land x0_3 1) <> 0)) (PreH13 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH14 : (x3_4 < U64_MOD)) (PreH15 : (0 <= x3_4)) (PreH16 : (x2_4 < U64_MOD)) (PreH17 : (0 <= x2_4)) (PreH18 : (x1_4 < U64_MOD)) (PreH19 : (0 <= x1_4)) (PreH20 : (x0_4 < U64_MOD)) (PreH21 : (0 <= x0_4)) (PreH22 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH23 : (x3_3 < U64_MOD)) (PreH24 : (0 <= x3_3)) (PreH25 : (x2_3 < U64_MOD)) (PreH26 : (0 <= x2_3)) (PreH27 : (x1_3 < U64_MOD)) (PreH28 : (0 <= x1_3)) (PreH29 : (x0_3 < U64_MOD)) (PreH30 : (0 <= x0_3)) (PreH31 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH32 : (x3_2 < U64_MOD)) (PreH33 : (0 <= x3_2)) (PreH34 : (x2_2 < U64_MOD)) (PreH35 : (0 <= x2_2)) (PreH36 : (x1_2 < U64_MOD)) (PreH37 : (0 <= x1_2)) (PreH38 : (x0_2 < U64_MOD)) (PreH39 : (0 <= x0_2)) (PreH40 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH41 : (x3 < U64_MOD)) (PreH42 : (0 <= x3)) (PreH43 : (x2 < U64_MOD)) (PreH44 : (0 <= x2)) (PreH45 : (x1 < U64_MOD)) (PreH46 : (0 <= x1)) (PreH47 : (x0 < U64_MOD)) (PreH48 : (0 <= x0)) (PreH49 : (retval = 0)) (PreH50 : (0 <= retval)) (PreH51 : (retval <= 1)) (PreH52 : (retval = 0)) (PreH53 : (Vi <> 0)) (PreH54 : (result_pre = a_pre)) (PreH55 : (i = 0)) (PreH56 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH57 : (retval_2 = 0)) ,
  (store_u256 ( &( "v" ) ) S )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vi - Ui ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "v" ) ) S )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_33_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Vn - Un ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vn <> 0)) (PreH53 : (i = 0)) (PreH54 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH55 : (retval_2 = 0)) ,
  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "s" ) ) = ( &( "s" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_33_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Vn - Un ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vn <> 0)) (PreH53 : (i = 0)) (PreH54 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH55 : (retval_2 = 0)) ,
  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "s" ) ) = ( &( "s" ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vn - Un ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_33_non_alias := MontgInvModp_partial_solve_wit_33_non_alias_pure -> MontgInvModp_partial_solve_wit_33_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_34_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Vi - Ui ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vi <> 0)) (PreH53 : (result_pre = a_pre)) (PreH54 : (i = 0)) (PreH55 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH56 : (retval_2 = 0)) ,
  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "s" ) ) = ( &( "s" ) )) ”
.

Definition MontgInvModp_partial_solve_wit_34_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : ((Vi - Ui ) = (S - (borrow * U256_MOD ) ))) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH10 : ((Z.land x0_4 1) <> 0)) (PreH11 : ((Z.land x0_3 1) <> 0)) (PreH12 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH13 : (x3_4 < U64_MOD)) (PreH14 : (0 <= x3_4)) (PreH15 : (x2_4 < U64_MOD)) (PreH16 : (0 <= x2_4)) (PreH17 : (x1_4 < U64_MOD)) (PreH18 : (0 <= x1_4)) (PreH19 : (x0_4 < U64_MOD)) (PreH20 : (0 <= x0_4)) (PreH21 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH22 : (x3_3 < U64_MOD)) (PreH23 : (0 <= x3_3)) (PreH24 : (x2_3 < U64_MOD)) (PreH25 : (0 <= x2_3)) (PreH26 : (x1_3 < U64_MOD)) (PreH27 : (0 <= x1_3)) (PreH28 : (x0_3 < U64_MOD)) (PreH29 : (0 <= x0_3)) (PreH30 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH31 : (x3_2 < U64_MOD)) (PreH32 : (0 <= x3_2)) (PreH33 : (x2_2 < U64_MOD)) (PreH34 : (0 <= x2_2)) (PreH35 : (x1_2 < U64_MOD)) (PreH36 : (0 <= x1_2)) (PreH37 : (x0_2 < U64_MOD)) (PreH38 : (0 <= x0_2)) (PreH39 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH40 : (x3 < U64_MOD)) (PreH41 : (0 <= x3)) (PreH42 : (x2 < U64_MOD)) (PreH43 : (0 <= x2)) (PreH44 : (x1 < U64_MOD)) (PreH45 : (0 <= x1)) (PreH46 : (x0 < U64_MOD)) (PreH47 : (0 <= x0)) (PreH48 : (retval = 0)) (PreH49 : (0 <= retval)) (PreH50 : (retval <= 1)) (PreH51 : (retval = 0)) (PreH52 : (Vi <> 0)) (PreH53 : (result_pre = a_pre)) (PreH54 : (i = 0)) (PreH55 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH56 : (retval_2 = 0)) ,
  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "s" ) ) = ( &( "s" ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vi - Ui ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_34_in_place := MontgInvModp_partial_solve_wit_34_in_place_pure -> MontgInvModp_partial_solve_wit_34_in_place_aux.

Definition MontgInvModp_partial_solve_wit_35_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Un: Z) (Vn: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (S_2: Z) (retval_3: Z) (PreH1 : (0 <= S_2)) (PreH2 : (S_2 < U256_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((Rn + Sn ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH6 : (( &( "s" ) ) = ( &( "s" ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow)) (PreH10 : (borrow <= 1)) (PreH11 : ((Vn - Un ) = (S - (borrow * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vn <> 0)) (PreH59 : (i = 0)) (PreH60 : (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry )) (PreH61 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S_2) ” 
  &&  “ (S_2 < U256_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((Rn + Sn ) = (S_2 + (retval_3 * U256_MOD ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vn - Un ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vn = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Un = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vn <> 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un Vn Rn Sn k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_36_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (k: Z) (carry: Z) (i: Z) (retval: Z) (Ui: Z) (Vi: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (retval_2: Z) (borrow: Z) (S: Z) (S_2: Z) (retval_3: Z) (PreH1 : (0 <= S_2)) (PreH2 : (S_2 < U256_MOD)) (PreH3 : (0 <= retval_3)) (PreH4 : (retval_3 <= 1)) (PreH5 : ((Ri + Si ) = (S_2 + (retval_3 * U256_MOD ) ))) (PreH6 : (( &( "s" ) ) = ( &( "s" ) ))) (PreH7 : (0 <= S)) (PreH8 : (S < U256_MOD)) (PreH9 : (0 <= borrow)) (PreH10 : (borrow <= 1)) (PreH11 : ((Vi - Ui ) = (S - (borrow * U256_MOD ) ))) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 0)) (PreH15 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH16 : ((Z.land x0_4 1) <> 0)) (PreH17 : ((Z.land x0_3 1) <> 0)) (PreH18 : (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH19 : (x3_4 < U64_MOD)) (PreH20 : (0 <= x3_4)) (PreH21 : (x2_4 < U64_MOD)) (PreH22 : (0 <= x2_4)) (PreH23 : (x1_4 < U64_MOD)) (PreH24 : (0 <= x1_4)) (PreH25 : (x0_4 < U64_MOD)) (PreH26 : (0 <= x0_4)) (PreH27 : (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH28 : (x3_3 < U64_MOD)) (PreH29 : (0 <= x3_3)) (PreH30 : (x2_3 < U64_MOD)) (PreH31 : (0 <= x2_3)) (PreH32 : (x1_3 < U64_MOD)) (PreH33 : (0 <= x1_3)) (PreH34 : (x0_3 < U64_MOD)) (PreH35 : (0 <= x0_3)) (PreH36 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH37 : (x3_2 < U64_MOD)) (PreH38 : (0 <= x3_2)) (PreH39 : (x2_2 < U64_MOD)) (PreH40 : (0 <= x2_2)) (PreH41 : (x1_2 < U64_MOD)) (PreH42 : (0 <= x1_2)) (PreH43 : (x0_2 < U64_MOD)) (PreH44 : (0 <= x0_2)) (PreH45 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH46 : (x3 < U64_MOD)) (PreH47 : (0 <= x3)) (PreH48 : (x2 < U64_MOD)) (PreH49 : (0 <= x2)) (PreH50 : (x1 < U64_MOD)) (PreH51 : (0 <= x1)) (PreH52 : (x0 < U64_MOD)) (PreH53 : (0 <= x0)) (PreH54 : (retval = 0)) (PreH55 : (0 <= retval)) (PreH56 : (retval <= 1)) (PreH57 : (retval = 0)) (PreH58 : (Vi <> 0)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry )) (PreH62 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 <= S_2) ” 
  &&  “ (S_2 < U256_MOD) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ ((Ri + Si ) = (S_2 + (retval_3 * U256_MOD ) )) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < U256_MOD) ” 
  &&  “ (0 <= borrow) ” 
  &&  “ (borrow <= 1) ” 
  &&  “ ((Vi - Ui ) = (S - (borrow * U256_MOD ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) <= (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ ((Z.land x0_4 1) <> 0) ” 
  &&  “ ((Z.land x0_3 1) <> 0) ” 
  &&  “ (Vi = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (Ui = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Vi <> 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui Vi Ri Si k carry ) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_u256 ( &( "v" ) ) (S ÷ 2 ) )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_37_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (carry > 0)) (PreH38 : (i = 0)) (PreH39 : (0 <= carry)) (PreH40 : (carry <= 1)) (PreH41 : (256 <= k)) (PreH42 : (k <= 512)) (PreH43 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH44 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (carry > 0)) (PreH74 : (i = 0)) (PreH75 : (0 <= carry)) (PreH76 : (carry <= 1)) (PreH77 : (256 <= k)) (PreH78 : (k <= 512)) (PreH79 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH80 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
).

Definition MontgInvModp_partial_solve_wit_37_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (carry > 0)) (PreH74 : (i = 0)) (PreH75 : (0 <= carry)) (PreH76 : (carry <= 1)) (PreH77 : (256 <= k)) (PreH78 : (k <= 512)) (PreH79 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH80 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
.

Definition MontgInvModp_partial_solve_wit_37_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (i: Z) (carry: Z) (k: Z) (Un: Z) (Rn: Z) (Sn: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (carry > 0)) (PreH38 : (i = 0)) (PreH39 : (0 <= carry)) (PreH40 : (carry <= 1)) (PreH41 : (256 <= k)) (PreH42 : (k <= 512)) (PreH43 : (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry )) (PreH44 : (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Rn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (carry > 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_non_alias Un 0 Rn Sn k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_non_alias Rn k carry ) ”
  &&  (store_u256 ( &( "r" ) ) Rn )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_37_non_alias := MontgInvModp_partial_solve_wit_37_non_alias_pure -> MontgInvModp_partial_solve_wit_37_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_38_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (carry > 0)) (PreH38 : (result_pre = a_pre)) (PreH39 : (i = 0)) (PreH40 : (0 <= carry)) (PreH41 : (carry <= 1)) (PreH42 : (256 <= k)) (PreH43 : (k <= 512)) (PreH44 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH45 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (carry > 0)) (PreH74 : (result_pre = a_pre)) (PreH75 : (i = 0)) (PreH76 : (0 <= carry)) (PreH77 : (carry <= 1)) (PreH78 : (256 <= k)) (PreH79 : (k <= 512)) (PreH80 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH81 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
).

Definition MontgInvModp_partial_solve_wit_38_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (carry > 0)) (PreH74 : (result_pre = a_pre)) (PreH75 : (i = 0)) (PreH76 : (0 <= carry)) (PreH77 : (carry <= 1)) (PreH78 : (256 <= k)) (PreH79 : (k <= 512)) (PreH80 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH81 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
.

Definition MontgInvModp_partial_solve_wit_38_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (i: Z) (carry: Z) (k: Z) (Ui: Z) (Ri: Z) (Si: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (carry > 0)) (PreH38 : (result_pre = a_pre)) (PreH39 : (i = 0)) (PreH40 : (0 <= carry)) (PreH41 : (carry <= 1)) (PreH42 : (256 <= k)) (PreH43 : (k <= 512)) (PreH44 : (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry )) (PreH45 : (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ” 
  &&  “ (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Ri = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (carry > 0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_phase1_state A_in_place Ui 0 Ri Si k carry ) ” 
  &&  “ (sm2p_mont_inv_phase1_exit_carry A_in_place Ri k carry ) ”
  &&  (store_u256 ( &( "r" ) ) Ri )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_38_in_place := MontgInvModp_partial_solve_wit_38_in_place_pure -> MontgInvModp_partial_solve_wit_38_in_place_aux.

Definition MontgInvModp_partial_solve_wit_39_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (i = 0)) (PreH38 : (0 <= carry)) (PreH39 : (carry <= 1)) (PreH40 : (256 <= k)) (PreH41 : (k <= 512)) (PreH42 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_40_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre = a_pre)) (PreH38 : (i = 0)) (PreH39 : (0 <= carry)) (PreH40 : (carry <= 1)) (PreH41 : (256 <= k)) (PreH42 : (k <= 512)) (PreH43 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R2i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ”
  &&  (store_u256 ( &( "r" ) ) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) )
  **  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_41_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH2 : (x3_6 < U64_MOD)) (PreH3 : (0 <= x3_6)) (PreH4 : (x2_6 < U64_MOD)) (PreH5 : (0 <= x2_6)) (PreH6 : (x1_6 < U64_MOD)) (PreH7 : (0 <= x1_6)) (PreH8 : (x0_6 < U64_MOD)) (PreH9 : (0 <= x0_6)) (PreH10 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (retval = 1)) (PreH22 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH23 : (Un = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH24 : (x3_5 < U64_MOD)) (PreH25 : (0 <= x3_5)) (PreH26 : (x2_5 < U64_MOD)) (PreH27 : (0 <= x2_5)) (PreH28 : (x1_5 < U64_MOD)) (PreH29 : (0 <= x1_5)) (PreH30 : (x0_5 < U64_MOD)) (PreH31 : (0 <= x0_5)) (PreH32 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH33 : (x3_4 < U64_MOD)) (PreH34 : (0 <= x3_4)) (PreH35 : (x2_4 < U64_MOD)) (PreH36 : (0 <= x2_4)) (PreH37 : (x1_4 < U64_MOD)) (PreH38 : (0 <= x1_4)) (PreH39 : (x0_4 < U64_MOD)) (PreH40 : (0 <= x0_4)) (PreH41 : (R2n = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH42 : (x3_3 < U64_MOD)) (PreH43 : (0 <= x3_3)) (PreH44 : (x2_3 < U64_MOD)) (PreH45 : (0 <= x2_3)) (PreH46 : (x1_3 < U64_MOD)) (PreH47 : (0 <= x1_3)) (PreH48 : (x0_3 < U64_MOD)) (PreH49 : (0 <= x0_3)) (PreH50 : (Sn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (i = 0)) (PreH60 : (0 <= carry)) (PreH61 : (carry <= 1)) (PreH62 : (256 <= k)) (PreH63 : (k <= 512)) (PreH64 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH65 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (x0_4 <= UINT64_MAX)) (PreH8 : (x1_4 <= UINT64_MAX)) (PreH9 : (x2_4 <= UINT64_MAX)) (PreH10 : (x3_4 <= UINT64_MAX)) (PreH11 : (x0_5 <= UINT64_MAX)) (PreH12 : (x1_5 <= UINT64_MAX)) (PreH13 : (x2_5 <= UINT64_MAX)) (PreH14 : (x3_5 <= UINT64_MAX)) (PreH15 : (x0 <= UINT64_MAX)) (PreH16 : (x1 <= UINT64_MAX)) (PreH17 : (x2 <= UINT64_MAX)) (PreH18 : (x3 <= UINT64_MAX)) (PreH19 : (x0_6 <= UINT64_MAX)) (PreH20 : (x1_6 <= UINT64_MAX)) (PreH21 : (x2_6 <= UINT64_MAX)) (PreH22 : (x3_6 <= UINT64_MAX)) (PreH23 : (k >= 0)) (PreH24 : (i >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_4 >= 0)) (PreH30 : (x1_4 >= 0)) (PreH31 : (x2_4 >= 0)) (PreH32 : (x3_4 >= 0)) (PreH33 : (x0_5 >= 0)) (PreH34 : (x1_5 >= 0)) (PreH35 : (x2_5 >= 0)) (PreH36 : (x3_5 >= 0)) (PreH37 : (x0 >= 0)) (PreH38 : (x1 >= 0)) (PreH39 : (x2 >= 0)) (PreH40 : (x3 >= 0)) (PreH41 : (x0_6 >= 0)) (PreH42 : (x1_6 >= 0)) (PreH43 : (x2_6 >= 0)) (PreH44 : (x3_6 >= 0)) (PreH45 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH46 : (x3_6 < U64_MOD)) (PreH47 : (0 <= x3_6)) (PreH48 : (x2_6 < U64_MOD)) (PreH49 : (0 <= x2_6)) (PreH50 : (x1_6 < U64_MOD)) (PreH51 : (0 <= x1_6)) (PreH52 : (x0_6 < U64_MOD)) (PreH53 : (0 <= x0_6)) (PreH54 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (0 <= retval)) (PreH64 : (retval <= 1)) (PreH65 : (retval = 1)) (PreH66 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH67 : (Un = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH68 : (x3_5 < U64_MOD)) (PreH69 : (0 <= x3_5)) (PreH70 : (x2_5 < U64_MOD)) (PreH71 : (0 <= x2_5)) (PreH72 : (x1_5 < U64_MOD)) (PreH73 : (0 <= x1_5)) (PreH74 : (x0_5 < U64_MOD)) (PreH75 : (0 <= x0_5)) (PreH76 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH77 : (x3_4 < U64_MOD)) (PreH78 : (0 <= x3_4)) (PreH79 : (x2_4 < U64_MOD)) (PreH80 : (0 <= x2_4)) (PreH81 : (x1_4 < U64_MOD)) (PreH82 : (0 <= x1_4)) (PreH83 : (x0_4 < U64_MOD)) (PreH84 : (0 <= x0_4)) (PreH85 : (R2n = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH86 : (x3_3 < U64_MOD)) (PreH87 : (0 <= x3_3)) (PreH88 : (x2_3 < U64_MOD)) (PreH89 : (0 <= x2_3)) (PreH90 : (x1_3 < U64_MOD)) (PreH91 : (0 <= x1_3)) (PreH92 : (x0_3 < U64_MOD)) (PreH93 : (0 <= x0_3)) (PreH94 : (Sn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH95 : (x3_2 < U64_MOD)) (PreH96 : (0 <= x3_2)) (PreH97 : (x2_2 < U64_MOD)) (PreH98 : (0 <= x2_2)) (PreH99 : (x1_2 < U64_MOD)) (PreH100 : (0 <= x1_2)) (PreH101 : (x0_2 < U64_MOD)) (PreH102 : (0 <= x0_2)) (PreH103 : (i = 0)) (PreH104 : (0 <= carry)) (PreH105 : (carry <= 1)) (PreH106 : (256 <= k)) (PreH107 : (k <= 512)) (PreH108 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH109 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ”
).

Definition MontgInvModp_partial_solve_wit_41_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (x0_4 <= UINT64_MAX)) (PreH8 : (x1_4 <= UINT64_MAX)) (PreH9 : (x2_4 <= UINT64_MAX)) (PreH10 : (x3_4 <= UINT64_MAX)) (PreH11 : (x0_5 <= UINT64_MAX)) (PreH12 : (x1_5 <= UINT64_MAX)) (PreH13 : (x2_5 <= UINT64_MAX)) (PreH14 : (x3_5 <= UINT64_MAX)) (PreH15 : (x0 <= UINT64_MAX)) (PreH16 : (x1 <= UINT64_MAX)) (PreH17 : (x2 <= UINT64_MAX)) (PreH18 : (x3 <= UINT64_MAX)) (PreH19 : (x0_6 <= UINT64_MAX)) (PreH20 : (x1_6 <= UINT64_MAX)) (PreH21 : (x2_6 <= UINT64_MAX)) (PreH22 : (x3_6 <= UINT64_MAX)) (PreH23 : (k >= 0)) (PreH24 : (i >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_4 >= 0)) (PreH30 : (x1_4 >= 0)) (PreH31 : (x2_4 >= 0)) (PreH32 : (x3_4 >= 0)) (PreH33 : (x0_5 >= 0)) (PreH34 : (x1_5 >= 0)) (PreH35 : (x2_5 >= 0)) (PreH36 : (x3_5 >= 0)) (PreH37 : (x0 >= 0)) (PreH38 : (x1 >= 0)) (PreH39 : (x2 >= 0)) (PreH40 : (x3 >= 0)) (PreH41 : (x0_6 >= 0)) (PreH42 : (x1_6 >= 0)) (PreH43 : (x2_6 >= 0)) (PreH44 : (x3_6 >= 0)) (PreH45 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH46 : (x3_6 < U64_MOD)) (PreH47 : (0 <= x3_6)) (PreH48 : (x2_6 < U64_MOD)) (PreH49 : (0 <= x2_6)) (PreH50 : (x1_6 < U64_MOD)) (PreH51 : (0 <= x1_6)) (PreH52 : (x0_6 < U64_MOD)) (PreH53 : (0 <= x0_6)) (PreH54 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (0 <= retval)) (PreH64 : (retval <= 1)) (PreH65 : (retval = 1)) (PreH66 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH67 : (Un = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH68 : (x3_5 < U64_MOD)) (PreH69 : (0 <= x3_5)) (PreH70 : (x2_5 < U64_MOD)) (PreH71 : (0 <= x2_5)) (PreH72 : (x1_5 < U64_MOD)) (PreH73 : (0 <= x1_5)) (PreH74 : (x0_5 < U64_MOD)) (PreH75 : (0 <= x0_5)) (PreH76 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH77 : (x3_4 < U64_MOD)) (PreH78 : (0 <= x3_4)) (PreH79 : (x2_4 < U64_MOD)) (PreH80 : (0 <= x2_4)) (PreH81 : (x1_4 < U64_MOD)) (PreH82 : (0 <= x1_4)) (PreH83 : (x0_4 < U64_MOD)) (PreH84 : (0 <= x0_4)) (PreH85 : (R2n = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH86 : (x3_3 < U64_MOD)) (PreH87 : (0 <= x3_3)) (PreH88 : (x2_3 < U64_MOD)) (PreH89 : (0 <= x2_3)) (PreH90 : (x1_3 < U64_MOD)) (PreH91 : (0 <= x1_3)) (PreH92 : (x0_3 < U64_MOD)) (PreH93 : (0 <= x0_3)) (PreH94 : (Sn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH95 : (x3_2 < U64_MOD)) (PreH96 : (0 <= x3_2)) (PreH97 : (x2_2 < U64_MOD)) (PreH98 : (0 <= x2_2)) (PreH99 : (x1_2 < U64_MOD)) (PreH100 : (0 <= x1_2)) (PreH101 : (x0_2 < U64_MOD)) (PreH102 : (0 <= x0_2)) (PreH103 : (i = 0)) (PreH104 : (0 <= carry)) (PreH105 : (carry <= 1)) (PreH106 : (256 <= k)) (PreH107 : (k <= 512)) (PreH108 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH109 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ”
.

Definition MontgInvModp_partial_solve_wit_41_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R2n: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH2 : (x3_6 < U64_MOD)) (PreH3 : (0 <= x3_6)) (PreH4 : (x2_6 < U64_MOD)) (PreH5 : (0 <= x2_6)) (PreH6 : (x1_6 < U64_MOD)) (PreH7 : (0 <= x1_6)) (PreH8 : (x0_6 < U64_MOD)) (PreH9 : (0 <= x0_6)) (PreH10 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (retval = 1)) (PreH22 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH23 : (Un = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH24 : (x3_5 < U64_MOD)) (PreH25 : (0 <= x3_5)) (PreH26 : (x2_5 < U64_MOD)) (PreH27 : (0 <= x2_5)) (PreH28 : (x1_5 < U64_MOD)) (PreH29 : (0 <= x1_5)) (PreH30 : (x0_5 < U64_MOD)) (PreH31 : (0 <= x0_5)) (PreH32 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH33 : (x3_4 < U64_MOD)) (PreH34 : (0 <= x3_4)) (PreH35 : (x2_4 < U64_MOD)) (PreH36 : (0 <= x2_4)) (PreH37 : (x1_4 < U64_MOD)) (PreH38 : (0 <= x1_4)) (PreH39 : (x0_4 < U64_MOD)) (PreH40 : (0 <= x0_4)) (PreH41 : (R2n = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH42 : (x3_3 < U64_MOD)) (PreH43 : (0 <= x3_3)) (PreH44 : (x2_3 < U64_MOD)) (PreH45 : (0 <= x2_3)) (PreH46 : (x1_3 < U64_MOD)) (PreH47 : (0 <= x1_3)) (PreH48 : (x0_3 < U64_MOD)) (PreH49 : (0 <= x0_3)) (PreH50 : (Sn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (i = 0)) (PreH60 : (0 <= carry)) (PreH61 : (carry <= 1)) (PreH62 : (256 <= k)) (PreH63 : (k <= 512)) (PreH64 : (sm2p_mont_inv_post_loop_residue A_non_alias R2n k )) (PreH65 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Un = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (R2n = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Sn = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_non_alias R2n k ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "r" ) ) R2n )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_41_non_alias := MontgInvModp_partial_solve_wit_41_non_alias_pure -> MontgInvModp_partial_solve_wit_41_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_42_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH2 : (x3_6 < U64_MOD)) (PreH3 : (0 <= x3_6)) (PreH4 : (x2_6 < U64_MOD)) (PreH5 : (0 <= x2_6)) (PreH6 : (x1_6 < U64_MOD)) (PreH7 : (0 <= x1_6)) (PreH8 : (x0_6 < U64_MOD)) (PreH9 : (0 <= x0_6)) (PreH10 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (retval = 1)) (PreH22 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH23 : (Ui = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH24 : (x3_5 < U64_MOD)) (PreH25 : (0 <= x3_5)) (PreH26 : (x2_5 < U64_MOD)) (PreH27 : (0 <= x2_5)) (PreH28 : (x1_5 < U64_MOD)) (PreH29 : (0 <= x1_5)) (PreH30 : (x0_5 < U64_MOD)) (PreH31 : (0 <= x0_5)) (PreH32 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH33 : (x3_4 < U64_MOD)) (PreH34 : (0 <= x3_4)) (PreH35 : (x2_4 < U64_MOD)) (PreH36 : (0 <= x2_4)) (PreH37 : (x1_4 < U64_MOD)) (PreH38 : (0 <= x1_4)) (PreH39 : (x0_4 < U64_MOD)) (PreH40 : (0 <= x0_4)) (PreH41 : (R2i = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH42 : (x3_3 < U64_MOD)) (PreH43 : (0 <= x3_3)) (PreH44 : (x2_3 < U64_MOD)) (PreH45 : (0 <= x2_3)) (PreH46 : (x1_3 < U64_MOD)) (PreH47 : (0 <= x1_3)) (PreH48 : (x0_3 < U64_MOD)) (PreH49 : (0 <= x0_3)) (PreH50 : (Si = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (0 <= carry)) (PreH62 : (carry <= 1)) (PreH63 : (256 <= k)) (PreH64 : (k <= 512)) (PreH65 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH66 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (x0_4 <= UINT64_MAX)) (PreH8 : (x1_4 <= UINT64_MAX)) (PreH9 : (x2_4 <= UINT64_MAX)) (PreH10 : (x3_4 <= UINT64_MAX)) (PreH11 : (x0_5 <= UINT64_MAX)) (PreH12 : (x1_5 <= UINT64_MAX)) (PreH13 : (x2_5 <= UINT64_MAX)) (PreH14 : (x3_5 <= UINT64_MAX)) (PreH15 : (x0 <= UINT64_MAX)) (PreH16 : (x1 <= UINT64_MAX)) (PreH17 : (x2 <= UINT64_MAX)) (PreH18 : (x3 <= UINT64_MAX)) (PreH19 : (x0_6 <= UINT64_MAX)) (PreH20 : (x1_6 <= UINT64_MAX)) (PreH21 : (x2_6 <= UINT64_MAX)) (PreH22 : (x3_6 <= UINT64_MAX)) (PreH23 : (k >= 0)) (PreH24 : (i >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_4 >= 0)) (PreH30 : (x1_4 >= 0)) (PreH31 : (x2_4 >= 0)) (PreH32 : (x3_4 >= 0)) (PreH33 : (x0_5 >= 0)) (PreH34 : (x1_5 >= 0)) (PreH35 : (x2_5 >= 0)) (PreH36 : (x3_5 >= 0)) (PreH37 : (x0 >= 0)) (PreH38 : (x1 >= 0)) (PreH39 : (x2 >= 0)) (PreH40 : (x3 >= 0)) (PreH41 : (x0_6 >= 0)) (PreH42 : (x1_6 >= 0)) (PreH43 : (x2_6 >= 0)) (PreH44 : (x3_6 >= 0)) (PreH45 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH46 : (x3_6 < U64_MOD)) (PreH47 : (0 <= x3_6)) (PreH48 : (x2_6 < U64_MOD)) (PreH49 : (0 <= x2_6)) (PreH50 : (x1_6 < U64_MOD)) (PreH51 : (0 <= x1_6)) (PreH52 : (x0_6 < U64_MOD)) (PreH53 : (0 <= x0_6)) (PreH54 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (0 <= retval)) (PreH64 : (retval <= 1)) (PreH65 : (retval = 1)) (PreH66 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH67 : (Ui = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH68 : (x3_5 < U64_MOD)) (PreH69 : (0 <= x3_5)) (PreH70 : (x2_5 < U64_MOD)) (PreH71 : (0 <= x2_5)) (PreH72 : (x1_5 < U64_MOD)) (PreH73 : (0 <= x1_5)) (PreH74 : (x0_5 < U64_MOD)) (PreH75 : (0 <= x0_5)) (PreH76 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH77 : (x3_4 < U64_MOD)) (PreH78 : (0 <= x3_4)) (PreH79 : (x2_4 < U64_MOD)) (PreH80 : (0 <= x2_4)) (PreH81 : (x1_4 < U64_MOD)) (PreH82 : (0 <= x1_4)) (PreH83 : (x0_4 < U64_MOD)) (PreH84 : (0 <= x0_4)) (PreH85 : (R2i = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH86 : (x3_3 < U64_MOD)) (PreH87 : (0 <= x3_3)) (PreH88 : (x2_3 < U64_MOD)) (PreH89 : (0 <= x2_3)) (PreH90 : (x1_3 < U64_MOD)) (PreH91 : (0 <= x1_3)) (PreH92 : (x0_3 < U64_MOD)) (PreH93 : (0 <= x0_3)) (PreH94 : (Si = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH95 : (x3_2 < U64_MOD)) (PreH96 : (0 <= x3_2)) (PreH97 : (x2_2 < U64_MOD)) (PreH98 : (0 <= x2_2)) (PreH99 : (x1_2 < U64_MOD)) (PreH100 : (0 <= x1_2)) (PreH101 : (x0_2 < U64_MOD)) (PreH102 : (0 <= x0_2)) (PreH103 : (result_pre = a_pre)) (PreH104 : (i = 0)) (PreH105 : (0 <= carry)) (PreH106 : (carry <= 1)) (PreH107 : (256 <= k)) (PreH108 : (k <= 512)) (PreH109 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH110 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ”
).

Definition MontgInvModp_partial_solve_wit_42_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0_2 <= UINT64_MAX)) (PreH4 : (x1_2 <= UINT64_MAX)) (PreH5 : (x2_2 <= UINT64_MAX)) (PreH6 : (x3_2 <= UINT64_MAX)) (PreH7 : (x0_4 <= UINT64_MAX)) (PreH8 : (x1_4 <= UINT64_MAX)) (PreH9 : (x2_4 <= UINT64_MAX)) (PreH10 : (x3_4 <= UINT64_MAX)) (PreH11 : (x0_5 <= UINT64_MAX)) (PreH12 : (x1_5 <= UINT64_MAX)) (PreH13 : (x2_5 <= UINT64_MAX)) (PreH14 : (x3_5 <= UINT64_MAX)) (PreH15 : (x0 <= UINT64_MAX)) (PreH16 : (x1 <= UINT64_MAX)) (PreH17 : (x2 <= UINT64_MAX)) (PreH18 : (x3 <= UINT64_MAX)) (PreH19 : (x0_6 <= UINT64_MAX)) (PreH20 : (x1_6 <= UINT64_MAX)) (PreH21 : (x2_6 <= UINT64_MAX)) (PreH22 : (x3_6 <= UINT64_MAX)) (PreH23 : (k >= 0)) (PreH24 : (i >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_4 >= 0)) (PreH30 : (x1_4 >= 0)) (PreH31 : (x2_4 >= 0)) (PreH32 : (x3_4 >= 0)) (PreH33 : (x0_5 >= 0)) (PreH34 : (x1_5 >= 0)) (PreH35 : (x2_5 >= 0)) (PreH36 : (x3_5 >= 0)) (PreH37 : (x0 >= 0)) (PreH38 : (x1 >= 0)) (PreH39 : (x2 >= 0)) (PreH40 : (x3 >= 0)) (PreH41 : (x0_6 >= 0)) (PreH42 : (x1_6 >= 0)) (PreH43 : (x2_6 >= 0)) (PreH44 : (x3_6 >= 0)) (PreH45 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH46 : (x3_6 < U64_MOD)) (PreH47 : (0 <= x3_6)) (PreH48 : (x2_6 < U64_MOD)) (PreH49 : (0 <= x2_6)) (PreH50 : (x1_6 < U64_MOD)) (PreH51 : (0 <= x1_6)) (PreH52 : (x0_6 < U64_MOD)) (PreH53 : (0 <= x0_6)) (PreH54 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH55 : (x3 < U64_MOD)) (PreH56 : (0 <= x3)) (PreH57 : (x2 < U64_MOD)) (PreH58 : (0 <= x2)) (PreH59 : (x1 < U64_MOD)) (PreH60 : (0 <= x1)) (PreH61 : (x0 < U64_MOD)) (PreH62 : (0 <= x0)) (PreH63 : (0 <= retval)) (PreH64 : (retval <= 1)) (PreH65 : (retval = 1)) (PreH66 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH67 : (Ui = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH68 : (x3_5 < U64_MOD)) (PreH69 : (0 <= x3_5)) (PreH70 : (x2_5 < U64_MOD)) (PreH71 : (0 <= x2_5)) (PreH72 : (x1_5 < U64_MOD)) (PreH73 : (0 <= x1_5)) (PreH74 : (x0_5 < U64_MOD)) (PreH75 : (0 <= x0_5)) (PreH76 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH77 : (x3_4 < U64_MOD)) (PreH78 : (0 <= x3_4)) (PreH79 : (x2_4 < U64_MOD)) (PreH80 : (0 <= x2_4)) (PreH81 : (x1_4 < U64_MOD)) (PreH82 : (0 <= x1_4)) (PreH83 : (x0_4 < U64_MOD)) (PreH84 : (0 <= x0_4)) (PreH85 : (R2i = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH86 : (x3_3 < U64_MOD)) (PreH87 : (0 <= x3_3)) (PreH88 : (x2_3 < U64_MOD)) (PreH89 : (0 <= x2_3)) (PreH90 : (x1_3 < U64_MOD)) (PreH91 : (0 <= x1_3)) (PreH92 : (x0_3 < U64_MOD)) (PreH93 : (0 <= x0_3)) (PreH94 : (Si = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH95 : (x3_2 < U64_MOD)) (PreH96 : (0 <= x3_2)) (PreH97 : (x2_2 < U64_MOD)) (PreH98 : (0 <= x2_2)) (PreH99 : (x1_2 < U64_MOD)) (PreH100 : (0 <= x1_2)) (PreH101 : (x0_2 < U64_MOD)) (PreH102 : (0 <= x0_2)) (PreH103 : (result_pre = a_pre)) (PreH104 : (i = 0)) (PreH105 : (0 <= carry)) (PreH106 : (carry <= 1)) (PreH107 : (256 <= k)) (PreH108 : (k <= 512)) (PreH109 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH110 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ”
.

Definition MontgInvModp_partial_solve_wit_42_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R2i: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (x0_5: Z) (x1_5: Z) (x2_5: Z) (x3_5: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_6: Z) (x1_6: Z) (x2_6: Z) (x3_6: Z) (PreH1 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6)))) (PreH2 : (x3_6 < U64_MOD)) (PreH3 : (0 <= x3_6)) (PreH4 : (x2_6 < U64_MOD)) (PreH5 : (0 <= x2_6)) (PreH6 : (x1_6 < U64_MOD)) (PreH7 : (0 <= x1_6)) (PreH8 : (x0_6 < U64_MOD)) (PreH9 : (0 <= x0_6)) (PreH10 : ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (0 <= retval)) (PreH20 : (retval <= 1)) (PreH21 : (retval = 1)) (PreH22 : ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))))) (PreH23 : (Ui = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5)))) (PreH24 : (x3_5 < U64_MOD)) (PreH25 : (0 <= x3_5)) (PreH26 : (x2_5 < U64_MOD)) (PreH27 : (0 <= x2_5)) (PreH28 : (x1_5 < U64_MOD)) (PreH29 : (0 <= x1_5)) (PreH30 : (x0_5 < U64_MOD)) (PreH31 : (0 <= x0_5)) (PreH32 : (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH33 : (x3_4 < U64_MOD)) (PreH34 : (0 <= x3_4)) (PreH35 : (x2_4 < U64_MOD)) (PreH36 : (0 <= x2_4)) (PreH37 : (x1_4 < U64_MOD)) (PreH38 : (0 <= x1_4)) (PreH39 : (x0_4 < U64_MOD)) (PreH40 : (0 <= x0_4)) (PreH41 : (R2i = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH42 : (x3_3 < U64_MOD)) (PreH43 : (0 <= x3_3)) (PreH44 : (x2_3 < U64_MOD)) (PreH45 : (0 <= x2_3)) (PreH46 : (x1_3 < U64_MOD)) (PreH47 : (0 <= x1_3)) (PreH48 : (x0_3 < U64_MOD)) (PreH49 : (0 <= x0_3)) (PreH50 : (Si = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH51 : (x3_2 < U64_MOD)) (PreH52 : (0 <= x3_2)) (PreH53 : (x2_2 < U64_MOD)) (PreH54 : (0 <= x2_2)) (PreH55 : (x1_2 < U64_MOD)) (PreH56 : (0 <= x1_2)) (PreH57 : (x0_2 < U64_MOD)) (PreH58 : (0 <= x0_2)) (PreH59 : (result_pre = a_pre)) (PreH60 : (i = 0)) (PreH61 : (0 <= carry)) (PreH62 : (carry <= 1)) (PreH63 : (256 <= k)) (PreH64 : (k <= 512)) (PreH65 : (sm2p_mont_inv_post_loop_residue A_in_place R2i k )) (PreH66 : (retval <> 0)) ,
  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_6)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_6)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "SM2_P" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ (SM2_P_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) = (u256_of_limbs (x0_6) (x1_6) (x2_6) (x3_6))) ” 
  &&  “ (x3_6 < U64_MOD) ” 
  &&  “ (0 <= x3_6) ” 
  &&  “ (x2_6 < U64_MOD) ” 
  &&  “ (0 <= x2_6) ” 
  &&  “ (x1_6 < U64_MOD) ” 
  &&  “ (0 <= x1_6) ” 
  &&  “ (x0_6 < U64_MOD) ” 
  &&  “ (0 <= x0_6) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) >= (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z)))))))))))) ” 
  &&  “ (Ui = (u256_of_limbs (x0_5) (x1_5) (x2_5) (x3_5))) ” 
  &&  “ (x3_5 < U64_MOD) ” 
  &&  “ (0 <= x3_5) ” 
  &&  “ (x2_5 < U64_MOD) ” 
  &&  “ (0 <= x2_5) ” 
  &&  “ (x1_5 < U64_MOD) ” 
  &&  “ (0 <= x1_5) ” 
  &&  “ (x0_5 < U64_MOD) ” 
  &&  “ (0 <= x0_5) ” 
  &&  “ (0 = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (R2i = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (Si = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_residue A_in_place R2i k ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "r" ) ) R2i )
  **  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_5)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_5)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_42_in_place := MontgInvModp_partial_solve_wit_42_in_place_pure -> MontgInvModp_partial_solve_wit_42_in_place_aux.

Definition MontgInvModp_partial_solve_wit_43_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (i = 0)) (PreH38 : (0 <= carry)) (PreH39 : (carry <= 1)) (PreH40 : (256 <= k)) (PreH41 : (k <= 512)) (PreH42 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (i = 0)) (PreH74 : (0 <= carry)) (PreH75 : (carry <= 1)) (PreH76 : (256 <= k)) (PreH77 : (k <= 512)) (PreH78 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
).

Definition MontgInvModp_partial_solve_wit_43_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (i = 0)) (PreH74 : (0 <= carry)) (PreH75 : (carry <= 1)) (PreH76 : (256 <= k)) (PreH77 : (k <= 512)) (PreH78 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
.

Definition MontgInvModp_partial_solve_wit_43_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (i: Z) (carry: Z) (k: Z) (R4n: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Sn = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (i = 0)) (PreH38 : (0 <= carry)) (PreH39 : (carry <= 1)) (PreH40 : (256 <= k)) (PreH41 : (k <= 512)) (PreH42 : (sm2p_mont_inv_post_loop_norm A_non_alias R4n k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ” 
  &&  “ (Un = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R4n = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Sn = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_non_alias R4n k ) ”
  &&  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (store_u256 ( &( "r" ) ) R4n )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_43_non_alias := MontgInvModp_partial_solve_wit_43_non_alias_pure -> MontgInvModp_partial_solve_wit_43_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_44_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre = a_pre)) (PreH38 : (i = 0)) (PreH39 : (0 <= carry)) (PreH40 : (carry <= 1)) (PreH41 : (256 <= k)) (PreH42 : (k <= 512)) (PreH43 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (result_pre = a_pre)) (PreH74 : (i = 0)) (PreH75 : (0 <= carry)) (PreH76 : (carry <= 1)) (PreH77 : (256 <= k)) (PreH78 : (k <= 512)) (PreH79 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
).

Definition MontgInvModp_partial_solve_wit_44_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (k <= UINT64_MAX)) (PreH2 : (i <= UINT64_MAX)) (PreH3 : (x0 <= UINT64_MAX)) (PreH4 : (x1 <= UINT64_MAX)) (PreH5 : (x2 <= UINT64_MAX)) (PreH6 : (x3 <= UINT64_MAX)) (PreH7 : (x0_2 <= UINT64_MAX)) (PreH8 : (x1_2 <= UINT64_MAX)) (PreH9 : (x2_2 <= UINT64_MAX)) (PreH10 : (x3_2 <= UINT64_MAX)) (PreH11 : (x0_3 <= UINT64_MAX)) (PreH12 : (x1_3 <= UINT64_MAX)) (PreH13 : (x2_3 <= UINT64_MAX)) (PreH14 : (x3_3 <= UINT64_MAX)) (PreH15 : (x0_4 <= UINT64_MAX)) (PreH16 : (x1_4 <= UINT64_MAX)) (PreH17 : (x2_4 <= UINT64_MAX)) (PreH18 : (x3_4 <= UINT64_MAX)) (PreH19 : (k >= 0)) (PreH20 : (i >= 0)) (PreH21 : (x0 >= 0)) (PreH22 : (x1 >= 0)) (PreH23 : (x2 >= 0)) (PreH24 : (x3 >= 0)) (PreH25 : (x0_2 >= 0)) (PreH26 : (x1_2 >= 0)) (PreH27 : (x2_2 >= 0)) (PreH28 : (x3_2 >= 0)) (PreH29 : (x0_3 >= 0)) (PreH30 : (x1_3 >= 0)) (PreH31 : (x2_3 >= 0)) (PreH32 : (x3_3 >= 0)) (PreH33 : (x0_4 >= 0)) (PreH34 : (x1_4 >= 0)) (PreH35 : (x2_4 >= 0)) (PreH36 : (x3_4 >= 0)) (PreH37 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH38 : (x3_4 < U64_MOD)) (PreH39 : (0 <= x3_4)) (PreH40 : (x2_4 < U64_MOD)) (PreH41 : (0 <= x2_4)) (PreH42 : (x1_4 < U64_MOD)) (PreH43 : (0 <= x1_4)) (PreH44 : (x0_4 < U64_MOD)) (PreH45 : (0 <= x0_4)) (PreH46 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH47 : (x3_3 < U64_MOD)) (PreH48 : (0 <= x3_3)) (PreH49 : (x2_3 < U64_MOD)) (PreH50 : (0 <= x2_3)) (PreH51 : (x1_3 < U64_MOD)) (PreH52 : (0 <= x1_3)) (PreH53 : (x0_3 < U64_MOD)) (PreH54 : (0 <= x0_3)) (PreH55 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH56 : (x3_2 < U64_MOD)) (PreH57 : (0 <= x3_2)) (PreH58 : (x2_2 < U64_MOD)) (PreH59 : (0 <= x2_2)) (PreH60 : (x1_2 < U64_MOD)) (PreH61 : (0 <= x1_2)) (PreH62 : (x0_2 < U64_MOD)) (PreH63 : (0 <= x0_2)) (PreH64 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH65 : (x3 < U64_MOD)) (PreH66 : (0 <= x3)) (PreH67 : (x2 < U64_MOD)) (PreH68 : (0 <= x2)) (PreH69 : (x1 < U64_MOD)) (PreH70 : (0 <= x1)) (PreH71 : (x0 < U64_MOD)) (PreH72 : (0 <= x0)) (PreH73 : (result_pre = a_pre)) (PreH74 : (i = 0)) (PreH75 : (0 <= carry)) (PreH76 : (carry <= 1)) (PreH77 : (256 <= k)) (PreH78 : (k <= 512)) (PreH79 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
.

Definition MontgInvModp_partial_solve_wit_44_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (i: Z) (carry: Z) (k: Z) (R4i: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (x0_3: Z) (x1_3: Z) (x2_3: Z) (x3_3: Z) (x0_4: Z) (x1_4: Z) (x2_4: Z) (x3_4: Z) (PreH1 : (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4)))) (PreH2 : (x3_4 < U64_MOD)) (PreH3 : (0 <= x3_4)) (PreH4 : (x2_4 < U64_MOD)) (PreH5 : (0 <= x2_4)) (PreH6 : (x1_4 < U64_MOD)) (PreH7 : (0 <= x1_4)) (PreH8 : (x0_4 < U64_MOD)) (PreH9 : (0 <= x0_4)) (PreH10 : (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)))) (PreH11 : (x3_3 < U64_MOD)) (PreH12 : (0 <= x3_3)) (PreH13 : (x2_3 < U64_MOD)) (PreH14 : (0 <= x2_3)) (PreH15 : (x1_3 < U64_MOD)) (PreH16 : (0 <= x1_3)) (PreH17 : (x0_3 < U64_MOD)) (PreH18 : (0 <= x0_3)) (PreH19 : (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH20 : (x3_2 < U64_MOD)) (PreH21 : (0 <= x3_2)) (PreH22 : (x2_2 < U64_MOD)) (PreH23 : (0 <= x2_2)) (PreH24 : (x1_2 < U64_MOD)) (PreH25 : (0 <= x1_2)) (PreH26 : (x0_2 < U64_MOD)) (PreH27 : (0 <= x0_2)) (PreH28 : (Si = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH29 : (x3 < U64_MOD)) (PreH30 : (0 <= x3)) (PreH31 : (x2 < U64_MOD)) (PreH32 : (0 <= x2)) (PreH33 : (x1 < U64_MOD)) (PreH34 : (0 <= x1)) (PreH35 : (x0 < U64_MOD)) (PreH36 : (0 <= x0)) (PreH37 : (result_pre = a_pre)) (PreH38 : (i = 0)) (PreH39 : (0 <= carry)) (PreH40 : (carry <= 1)) (PreH41 : (256 <= k)) (PreH42 : (k <= 512)) (PreH43 : (sm2p_mont_inv_post_loop_norm A_in_place R4i k )) ,
  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "r" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&(( &( "r" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (( &( "r" ) ) = ( &( "r" ) )) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ” 
  &&  “ (Ui = (u256_of_limbs (x0_4) (x1_4) (x2_4) (x3_4))) ” 
  &&  “ (x3_4 < U64_MOD) ” 
  &&  “ (0 <= x3_4) ” 
  &&  “ (x2_4 < U64_MOD) ” 
  &&  “ (0 <= x2_4) ” 
  &&  “ (x1_4 < U64_MOD) ” 
  &&  “ (0 <= x1_4) ” 
  &&  “ (x0_4 < U64_MOD) ” 
  &&  “ (0 <= x0_4) ” 
  &&  “ (0 = (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ (R4i = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Si = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= k) ” 
  &&  “ (k <= 512) ” 
  &&  “ (sm2p_mont_inv_post_loop_norm A_in_place R4i k ) ”
  &&  (store_u256 ( &( "SM2_P" ) ) SM2_P_Z )
  **  (store_u256 ( &( "r" ) ) R4i )
  **  (((&(( &( "u" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_4)
  **  (((&(( &( "u" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_4)
  **  (((&(( &( "v" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&(( &( "v" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&(( &( "s" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&(( &( "s" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&(( &( "s" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&(( &( "s" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_fp a_pre A_in_place )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_44_in_place := MontgInvModp_partial_solve_wit_44_in_place_pure -> MontgInvModp_partial_solve_wit_44_in_place_aux.

Definition MontgInvModp_partial_solve_wit_45_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= K0n)) (PreH5 : (K0n <= 512)) (PreH6 : (K0n <> 256)) (PreH7 : (0 <= R5n)) (PreH8 : (R5n < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0n)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_45_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (i: Z) (carry: Z) (K0n: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (256 <= K0n)) (PreH5 : (K0n <= 512)) (PreH6 : (K0n <> 256)) (PreH7 : (0 <= R5n)) (PreH8 : (R5n < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= K0n) ” 
  &&  “ (K0n <= 512) ” 
  &&  “ (K0n <> 256) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n K0n ) ”
  &&  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_45_non_alias := MontgInvModp_partial_solve_wit_45_non_alias_pure -> MontgInvModp_partial_solve_wit_45_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_46_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0i)) (PreH6 : (K0i <= 512)) (PreH7 : (K0i <> 256)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "k" ) )) # UInt64  |-> K0i)
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_46_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (i: Z) (carry: Z) (K0i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (i = 0)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (256 <= K0i)) (PreH6 : (K0i <= 512)) (PreH7 : (K0i <> 256)) (PreH8 : (0 <= R5i)) (PreH9 : (R5i < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (0 = 0) ” 
  &&  “ (32 = 32) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (256 <= K0i) ” 
  &&  “ (K0i <= 512) ” 
  &&  “ (K0i <> 256) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i K0i ) ”
  &&  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_46_in_place := MontgInvModp_partial_solve_wit_46_in_place_pure -> MontgInvModp_partial_solve_wit_46_in_place_aux.

Definition MontgInvModp_partial_solve_wit_47_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH8 : (sm2p_mont_inv_phase2_index K0n i k )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
|--
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n K0n ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0n i k ) ”
  &&  (((&(( &( "t" ) )->ₛ "v") + (i * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "t" ) )->ₛ "v") i 0 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_48_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH9 : (sm2p_mont_inv_phase2_index K0i i k )) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UInt64Array.full &(( &( "t" ) )->ₛ "v") 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i K0i ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0i i k ) ”
  &&  (((&(( &( "t" ) )->ₛ "v") + (i * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.missing_i &(( &( "t" ) )->ₛ "v") i 0 4 (cons (0) ((cons (0) ((cons (0) ((cons (0) ((@nil Z))))))))) )
  **  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_49_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (K0n: Z) (carry: Z) (i: Z) (k: Z) (Tn: Z) (PreH1 : (0 <= carry)) (PreH2 : (carry <= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < 4)) (PreH5 : (0 <= k)) (PreH6 : (k < 64)) (PreH7 : (0 <= Tn)) (PreH8 : (Tn < SM2_P_Z)) (PreH9 : (sm2p_mont_inv_phase1_result A_non_alias R5n K0n )) (PreH10 : (sm2p_mont_inv_phase2_index K0n i k )) (PreH11 : (Tn = (Z.pow (2) ((512 - K0n ))))) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (store_u256 ( &( "t" ) ) Tn )
  **  (store_sm2_rhop )
|--
  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (0 <= Tn) ” 
  &&  “ (Tn < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n K0n ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0n i k ) ” 
  &&  “ (Tn = (Z.pow (2) ((512 - K0n )))) ”
  &&  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "t" ) ) Tn )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp a_pre A_non_alias )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Sn )
.

Definition MontgInvModp_partial_solve_wit_50_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (K0i: Z) (carry: Z) (i: Z) (k: Z) (Ti: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < 4)) (PreH6 : (0 <= k)) (PreH7 : (k < 64)) (PreH8 : (0 <= Ti)) (PreH9 : (Ti < SM2_P_Z)) (PreH10 : (sm2p_mont_inv_phase1_result A_in_place R5i K0i )) (PreH11 : (sm2p_mont_inv_phase2_index K0i i k )) (PreH12 : (Ti = (Z.pow (2) ((512 - K0i ))))) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (store_u256 ( &( "t" ) ) Ti )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 4) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < 64) ” 
  &&  “ (0 <= Ti) ” 
  &&  “ (Ti < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i K0i ) ” 
  &&  “ (sm2p_mont_inv_phase2_index K0i i k ) ” 
  &&  “ (Ti = (Z.pow (2) ((512 - K0i )))) ”
  &&  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "t" ) ) Ti )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Si )
.

Definition MontgInvModp_partial_solve_wit_51_non_alias_pure := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (k = 256)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (i = 0)) (PreH5 : (0 <= R5n)) (PreH6 : (R5n < SM2_P_Z)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n 256 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_51_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (Un: Z) (Sn: Z) (R5n: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (k = 256)) (PreH2 : (0 <= carry)) (PreH3 : (carry <= 1)) (PreH4 : (i = 0)) (PreH5 : (0 <= R5n)) (PreH6 : (R5n < SM2_P_Z)) (PreH7 : (sm2p_mont_inv_phase1_result A_non_alias R5n 256 )) ,
  (store_fp a_pre A_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5n )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= R5n) ” 
  &&  “ (R5n < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_non_alias R5n 256 ) ”
  &&  (store_u256 ( &( "r" ) ) R5n )
  **  (UndefStructPredu32 result_pre )
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Un )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Sn )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_51_non_alias := MontgInvModp_partial_solve_wit_51_non_alias_pure -> MontgInvModp_partial_solve_wit_51_non_alias_aux.

Definition MontgInvModp_partial_solve_wit_52_in_place_pure := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5i)) (PreH7 : (R5i < SM2_P_Z)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i 256 )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "k" ) )) # UInt64  |-> k)
  **  ((( &( "carry" ) )) # UChar  |-> carry)
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ”
.

Definition MontgInvModp_partial_solve_wit_52_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (Ui: Z) (Si: Z) (R5i: Z) (k: Z) (carry: Z) (i: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (k = 256)) (PreH3 : (0 <= carry)) (PreH4 : (carry <= 1)) (PreH5 : (i = 0)) (PreH6 : (0 <= R5i)) (PreH7 : (R5i < SM2_P_Z)) (PreH8 : (sm2p_mont_inv_phase1_result A_in_place R5i 256 )) ,
  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "r" ) ) R5i )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
|--
  “ (32 = 32) ” 
  &&  “ (result_pre = a_pre) ” 
  &&  “ (k = 256) ” 
  &&  “ (0 <= carry) ” 
  &&  “ (carry <= 1) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= R5i) ” 
  &&  “ (R5i < SM2_P_Z) ” 
  &&  “ (sm2p_mont_inv_phase1_result A_in_place R5i 256 ) ”
  &&  (store_u256 ( &( "r" ) ) R5i )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_p )
  **  (store_u256 ( &( "u" ) ) Ui )
  **  (store_u256 ( &( "v" ) ) 0 )
  **  (store_u256 ( &( "s" ) ) Si )
  **  (UndefStructPredu32 ( &( "t" ) ) )
  **  (store_sm2_rhop )
.

Definition MontgInvModp_partial_solve_wit_52_in_place := MontgInvModp_partial_solve_wit_52_in_place_pure -> MontgInvModp_partial_solve_wit_52_in_place_aux.

Definition MontgInvModp_derive_mont_in_place_by_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_mont_in_place: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (A_mont_in_place <> 0) ”
  &&  (store_fp a_pre A_mont_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_in_place: Z) ,
  (“ (result_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Z,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Z) ” 
  &&  “ (Z < SM2_P_Z) ” 
  &&  “ ((A_in_place * Z ) = (U256_MOD + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Z )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (EX Ainv,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_mont_in_place * Ainv )) (SM2_P_Z)) = 1) ”
  &&  (store_fp result_pre (mont_p (Ainv)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Definition MontgInvModp_derive_mont_non_alias_by_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_mont_non_alias: Z) ,
  “ (A_mont_non_alias <> 0) ”
  &&  (store_fp a_pre A_mont_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_non_alias: Z) ,
  (“ (A_non_alias <> 0) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Z,
  “ (0 <= Z) ” 
  &&  “ (Z < SM2_P_Z) ” 
  &&  “ ((A_non_alias * Z ) = (U256_MOD + (K * SM2_P_Z ) )) ”
  &&  (store_fp a_pre A_non_alias )
  **  (store_fp result_pre Z )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (EX Ainv,
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_mont_non_alias * Ainv )) (SM2_P_Z)) = 1) ”
  &&  (store_fp a_pre A_mont_non_alias )
  **  (store_fp result_pre (mont_p (Ainv)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_MontgInvModp_safety_wit_1_non_alias : MontgInvModp_safety_wit_1_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_2_in_place : MontgInvModp_safety_wit_2_in_place.
Axiom proof_of_MontgInvModp_safety_wit_3_non_alias : MontgInvModp_safety_wit_3_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_4_in_place : MontgInvModp_safety_wit_4_in_place.
Axiom proof_of_MontgInvModp_safety_wit_5_non_alias : MontgInvModp_safety_wit_5_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_6_in_place : MontgInvModp_safety_wit_6_in_place.
Axiom proof_of_MontgInvModp_safety_wit_7_non_alias : MontgInvModp_safety_wit_7_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_8_non_alias : MontgInvModp_safety_wit_8_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_9_in_place : MontgInvModp_safety_wit_9_in_place.
Axiom proof_of_MontgInvModp_safety_wit_10_in_place : MontgInvModp_safety_wit_10_in_place.
Axiom proof_of_MontgInvModp_safety_wit_11_non_alias : MontgInvModp_safety_wit_11_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_12_in_place : MontgInvModp_safety_wit_12_in_place.
Axiom proof_of_MontgInvModp_safety_wit_13_non_alias : MontgInvModp_safety_wit_13_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_14_non_alias : MontgInvModp_safety_wit_14_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_15_in_place : MontgInvModp_safety_wit_15_in_place.
Axiom proof_of_MontgInvModp_safety_wit_16_in_place : MontgInvModp_safety_wit_16_in_place.
Axiom proof_of_MontgInvModp_safety_wit_17_non_alias : MontgInvModp_safety_wit_17_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_18_non_alias : MontgInvModp_safety_wit_18_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_19_in_place : MontgInvModp_safety_wit_19_in_place.
Axiom proof_of_MontgInvModp_safety_wit_20_in_place : MontgInvModp_safety_wit_20_in_place.
Axiom proof_of_MontgInvModp_safety_wit_21_non_alias : MontgInvModp_safety_wit_21_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_22_in_place : MontgInvModp_safety_wit_22_in_place.
Axiom proof_of_MontgInvModp_safety_wit_23_non_alias : MontgInvModp_safety_wit_23_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_24_in_place : MontgInvModp_safety_wit_24_in_place.
Axiom proof_of_MontgInvModp_safety_wit_25_non_alias : MontgInvModp_safety_wit_25_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_26_non_alias : MontgInvModp_safety_wit_26_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_27_in_place : MontgInvModp_safety_wit_27_in_place.
Axiom proof_of_MontgInvModp_safety_wit_28_in_place : MontgInvModp_safety_wit_28_in_place.
Axiom proof_of_MontgInvModp_safety_wit_29_non_alias : MontgInvModp_safety_wit_29_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_30_in_place : MontgInvModp_safety_wit_30_in_place.
Axiom proof_of_MontgInvModp_safety_wit_31_in_place : MontgInvModp_safety_wit_31_in_place.
Axiom proof_of_MontgInvModp_safety_wit_32_non_alias : MontgInvModp_safety_wit_32_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_33_in_place : MontgInvModp_safety_wit_33_in_place.
Axiom proof_of_MontgInvModp_safety_wit_34_non_alias : MontgInvModp_safety_wit_34_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_35_in_place : MontgInvModp_safety_wit_35_in_place.
Axiom proof_of_MontgInvModp_safety_wit_36_non_alias : MontgInvModp_safety_wit_36_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_37_non_alias : MontgInvModp_safety_wit_37_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_38_in_place : MontgInvModp_safety_wit_38_in_place.
Axiom proof_of_MontgInvModp_safety_wit_39_non_alias : MontgInvModp_safety_wit_39_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_40_in_place : MontgInvModp_safety_wit_40_in_place.
Axiom proof_of_MontgInvModp_safety_wit_41_non_alias : MontgInvModp_safety_wit_41_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_42_in_place : MontgInvModp_safety_wit_42_in_place.
Axiom proof_of_MontgInvModp_safety_wit_43_non_alias : MontgInvModp_safety_wit_43_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_44_in_place : MontgInvModp_safety_wit_44_in_place.
Axiom proof_of_MontgInvModp_safety_wit_45_non_alias : MontgInvModp_safety_wit_45_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_46_in_place : MontgInvModp_safety_wit_46_in_place.
Axiom proof_of_MontgInvModp_safety_wit_47_non_alias : MontgInvModp_safety_wit_47_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_48_in_place : MontgInvModp_safety_wit_48_in_place.
Axiom proof_of_MontgInvModp_safety_wit_49_non_alias : MontgInvModp_safety_wit_49_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_50_in_place : MontgInvModp_safety_wit_50_in_place.
Axiom proof_of_MontgInvModp_safety_wit_51_non_alias : MontgInvModp_safety_wit_51_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_52_in_place : MontgInvModp_safety_wit_52_in_place.
Axiom proof_of_MontgInvModp_safety_wit_53_non_alias : MontgInvModp_safety_wit_53_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_54_non_alias : MontgInvModp_safety_wit_54_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_55_in_place : MontgInvModp_safety_wit_55_in_place.
Axiom proof_of_MontgInvModp_safety_wit_56_in_place : MontgInvModp_safety_wit_56_in_place.
Axiom proof_of_MontgInvModp_safety_wit_57_non_alias : MontgInvModp_safety_wit_57_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_58_non_alias : MontgInvModp_safety_wit_58_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_59_non_alias : MontgInvModp_safety_wit_59_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_60_in_place : MontgInvModp_safety_wit_60_in_place.
Axiom proof_of_MontgInvModp_safety_wit_61_in_place : MontgInvModp_safety_wit_61_in_place.
Axiom proof_of_MontgInvModp_safety_wit_62_in_place : MontgInvModp_safety_wit_62_in_place.
Axiom proof_of_MontgInvModp_safety_wit_63_non_alias : MontgInvModp_safety_wit_63_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_64_non_alias : MontgInvModp_safety_wit_64_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_65_in_place : MontgInvModp_safety_wit_65_in_place.
Axiom proof_of_MontgInvModp_safety_wit_66_in_place : MontgInvModp_safety_wit_66_in_place.
Axiom proof_of_MontgInvModp_safety_wit_67_non_alias : MontgInvModp_safety_wit_67_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_68_non_alias : MontgInvModp_safety_wit_68_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_69_in_place : MontgInvModp_safety_wit_69_in_place.
Axiom proof_of_MontgInvModp_safety_wit_70_in_place : MontgInvModp_safety_wit_70_in_place.
Axiom proof_of_MontgInvModp_safety_wit_71_non_alias : MontgInvModp_safety_wit_71_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_72_non_alias : MontgInvModp_safety_wit_72_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_73_in_place : MontgInvModp_safety_wit_73_in_place.
Axiom proof_of_MontgInvModp_safety_wit_74_in_place : MontgInvModp_safety_wit_74_in_place.
Axiom proof_of_MontgInvModp_safety_wit_75_non_alias : MontgInvModp_safety_wit_75_non_alias.
Axiom proof_of_MontgInvModp_safety_wit_76_in_place : MontgInvModp_safety_wit_76_in_place.
Axiom proof_of_MontgInvModp_entail_wit_1_1_non_alias : MontgInvModp_entail_wit_1_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_1_2_in_place : MontgInvModp_entail_wit_1_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_2_non_alias : MontgInvModp_entail_wit_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_3_in_place : MontgInvModp_entail_wit_3_in_place.
Axiom proof_of_MontgInvModp_entail_wit_4_1_non_alias : MontgInvModp_entail_wit_4_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_4_2_in_place : MontgInvModp_entail_wit_4_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_5_non_alias : MontgInvModp_entail_wit_5_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_6_in_place : MontgInvModp_entail_wit_6_in_place.
Axiom proof_of_MontgInvModp_entail_wit_7_non_alias : MontgInvModp_entail_wit_7_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_8_in_place : MontgInvModp_entail_wit_8_in_place.
Axiom proof_of_MontgInvModp_entail_wit_9_1_non_alias : MontgInvModp_entail_wit_9_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_9_2_non_alias : MontgInvModp_entail_wit_9_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_9_3_in_place : MontgInvModp_entail_wit_9_3_in_place.
Axiom proof_of_MontgInvModp_entail_wit_9_4_in_place : MontgInvModp_entail_wit_9_4_in_place.
Axiom proof_of_MontgInvModp_entail_wit_10_1_non_alias : MontgInvModp_entail_wit_10_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_10_2_non_alias : MontgInvModp_entail_wit_10_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_10_3_in_place : MontgInvModp_entail_wit_10_3_in_place.
Axiom proof_of_MontgInvModp_entail_wit_10_4_in_place : MontgInvModp_entail_wit_10_4_in_place.
Axiom proof_of_MontgInvModp_entail_wit_11_non_alias : MontgInvModp_entail_wit_11_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_12_in_place : MontgInvModp_entail_wit_12_in_place.
Axiom proof_of_MontgInvModp_entail_wit_13_non_alias : MontgInvModp_entail_wit_13_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_14_in_place : MontgInvModp_entail_wit_14_in_place.
Axiom proof_of_MontgInvModp_entail_wit_15_1_in_place : MontgInvModp_entail_wit_15_1_in_place.
Axiom proof_of_MontgInvModp_entail_wit_15_2_in_place : MontgInvModp_entail_wit_15_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_15_3_in_place : MontgInvModp_entail_wit_15_3_in_place.
Axiom proof_of_MontgInvModp_entail_wit_15_4_in_place : MontgInvModp_entail_wit_15_4_in_place.
Axiom proof_of_MontgInvModp_entail_wit_16_1_non_alias : MontgInvModp_entail_wit_16_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_16_2_non_alias : MontgInvModp_entail_wit_16_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_16_3_non_alias : MontgInvModp_entail_wit_16_3_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_16_4_non_alias : MontgInvModp_entail_wit_16_4_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_17_non_alias : MontgInvModp_entail_wit_17_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_18_in_place : MontgInvModp_entail_wit_18_in_place.
Axiom proof_of_MontgInvModp_entail_wit_19_1_non_alias : MontgInvModp_entail_wit_19_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_19_2_in_place : MontgInvModp_entail_wit_19_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_20_1_non_alias : MontgInvModp_entail_wit_20_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_20_2_in_place : MontgInvModp_entail_wit_20_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_21_non_alias : MontgInvModp_entail_wit_21_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_22_in_place : MontgInvModp_entail_wit_22_in_place.
Axiom proof_of_MontgInvModp_entail_wit_23_1_non_alias : MontgInvModp_entail_wit_23_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_23_2_non_alias : MontgInvModp_entail_wit_23_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_24_1_in_place : MontgInvModp_entail_wit_24_1_in_place.
Axiom proof_of_MontgInvModp_entail_wit_24_2_in_place : MontgInvModp_entail_wit_24_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_25_1_non_alias : MontgInvModp_entail_wit_25_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_25_2_in_place : MontgInvModp_entail_wit_25_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_26_1_non_alias : MontgInvModp_entail_wit_26_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_26_2_in_place : MontgInvModp_entail_wit_26_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_27_1_non_alias : MontgInvModp_entail_wit_27_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_27_2_non_alias : MontgInvModp_entail_wit_27_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_27_3_in_place : MontgInvModp_entail_wit_27_3_in_place.
Axiom proof_of_MontgInvModp_entail_wit_27_4_in_place : MontgInvModp_entail_wit_27_4_in_place.
Axiom proof_of_MontgInvModp_entail_wit_28_1_non_alias : MontgInvModp_entail_wit_28_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_28_2_non_alias : MontgInvModp_entail_wit_28_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_28_3_in_place : MontgInvModp_entail_wit_28_3_in_place.
Axiom proof_of_MontgInvModp_entail_wit_28_4_in_place : MontgInvModp_entail_wit_28_4_in_place.
Axiom proof_of_MontgInvModp_entail_wit_29_1_non_alias : MontgInvModp_entail_wit_29_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_29_2_in_place : MontgInvModp_entail_wit_29_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_30_non_alias : MontgInvModp_entail_wit_30_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_31_in_place : MontgInvModp_entail_wit_31_in_place.
Axiom proof_of_MontgInvModp_entail_wit_32_1_non_alias : MontgInvModp_entail_wit_32_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_32_2_non_alias : MontgInvModp_entail_wit_32_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_33_1_in_place : MontgInvModp_entail_wit_33_1_in_place.
Axiom proof_of_MontgInvModp_entail_wit_33_2_in_place : MontgInvModp_entail_wit_33_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_34_1_non_alias : MontgInvModp_entail_wit_34_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_34_2_in_place : MontgInvModp_entail_wit_34_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_35_1_non_alias : MontgInvModp_entail_wit_35_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_35_2_in_place : MontgInvModp_entail_wit_35_2_in_place.
Axiom proof_of_MontgInvModp_entail_wit_36_non_alias : MontgInvModp_entail_wit_36_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_37_in_place : MontgInvModp_entail_wit_37_in_place.
Axiom proof_of_MontgInvModp_entail_wit_38_non_alias : MontgInvModp_entail_wit_38_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_39_in_place : MontgInvModp_entail_wit_39_in_place.
Axiom proof_of_MontgInvModp_entail_wit_40_non_alias : MontgInvModp_entail_wit_40_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_41_in_place : MontgInvModp_entail_wit_41_in_place.
Axiom proof_of_MontgInvModp_entail_wit_42_non_alias : MontgInvModp_entail_wit_42_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_43_in_place : MontgInvModp_entail_wit_43_in_place.
Axiom proof_of_MontgInvModp_entail_wit_44_non_alias : MontgInvModp_entail_wit_44_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_45_in_place : MontgInvModp_entail_wit_45_in_place.
Axiom proof_of_MontgInvModp_entail_wit_46_non_alias : MontgInvModp_entail_wit_46_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_47_in_place : MontgInvModp_entail_wit_47_in_place.
Axiom proof_of_MontgInvModp_entail_wit_48_non_alias : MontgInvModp_entail_wit_48_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_49_in_place : MontgInvModp_entail_wit_49_in_place.
Axiom proof_of_MontgInvModp_entail_wit_50_1_non_alias : MontgInvModp_entail_wit_50_1_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_50_2_non_alias : MontgInvModp_entail_wit_50_2_non_alias.
Axiom proof_of_MontgInvModp_entail_wit_51_1_in_place : MontgInvModp_entail_wit_51_1_in_place.
Axiom proof_of_MontgInvModp_entail_wit_51_2_in_place : MontgInvModp_entail_wit_51_2_in_place.
Axiom proof_of_MontgInvModp_return_wit_1_non_alias : MontgInvModp_return_wit_1_non_alias.
Axiom proof_of_MontgInvModp_return_wit_2_in_place : MontgInvModp_return_wit_2_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_1_non_alias_pure : MontgInvModp_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_1_non_alias : MontgInvModp_partial_solve_wit_1_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_2_in_place_pure : MontgInvModp_partial_solve_wit_2_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_2_in_place : MontgInvModp_partial_solve_wit_2_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_3_non_alias_pure : MontgInvModp_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_3_non_alias : MontgInvModp_partial_solve_wit_3_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_4_in_place_pure : MontgInvModp_partial_solve_wit_4_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_4_in_place : MontgInvModp_partial_solve_wit_4_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_5_non_alias_pure : MontgInvModp_partial_solve_wit_5_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_5_non_alias : MontgInvModp_partial_solve_wit_5_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_6_in_place_pure : MontgInvModp_partial_solve_wit_6_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_6_in_place : MontgInvModp_partial_solve_wit_6_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_7_non_alias_pure : MontgInvModp_partial_solve_wit_7_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_7_non_alias : MontgInvModp_partial_solve_wit_7_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_8_in_place_pure : MontgInvModp_partial_solve_wit_8_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_8_in_place : MontgInvModp_partial_solve_wit_8_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_9_non_alias : MontgInvModp_partial_solve_wit_9_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_10_in_place : MontgInvModp_partial_solve_wit_10_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_11_in_place : MontgInvModp_partial_solve_wit_11_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_12_non_alias : MontgInvModp_partial_solve_wit_12_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_13_in_place : MontgInvModp_partial_solve_wit_13_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_14_non_alias : MontgInvModp_partial_solve_wit_14_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_15_non_alias : MontgInvModp_partial_solve_wit_15_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_16_in_place : MontgInvModp_partial_solve_wit_16_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_17_non_alias : MontgInvModp_partial_solve_wit_17_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_18_in_place : MontgInvModp_partial_solve_wit_18_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_19_non_alias : MontgInvModp_partial_solve_wit_19_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_20_in_place : MontgInvModp_partial_solve_wit_20_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_21_non_alias_pure : MontgInvModp_partial_solve_wit_21_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_21_non_alias : MontgInvModp_partial_solve_wit_21_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_22_in_place_pure : MontgInvModp_partial_solve_wit_22_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_22_in_place : MontgInvModp_partial_solve_wit_22_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_23_non_alias : MontgInvModp_partial_solve_wit_23_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_24_in_place : MontgInvModp_partial_solve_wit_24_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_25_non_alias_pure : MontgInvModp_partial_solve_wit_25_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_25_non_alias : MontgInvModp_partial_solve_wit_25_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_26_in_place_pure : MontgInvModp_partial_solve_wit_26_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_26_in_place : MontgInvModp_partial_solve_wit_26_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_27_non_alias : MontgInvModp_partial_solve_wit_27_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_28_in_place : MontgInvModp_partial_solve_wit_28_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_29_non_alias_pure : MontgInvModp_partial_solve_wit_29_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_29_non_alias : MontgInvModp_partial_solve_wit_29_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_30_in_place_pure : MontgInvModp_partial_solve_wit_30_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_30_in_place : MontgInvModp_partial_solve_wit_30_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_31_non_alias : MontgInvModp_partial_solve_wit_31_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_32_in_place : MontgInvModp_partial_solve_wit_32_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_33_non_alias_pure : MontgInvModp_partial_solve_wit_33_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_33_non_alias : MontgInvModp_partial_solve_wit_33_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_34_in_place_pure : MontgInvModp_partial_solve_wit_34_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_34_in_place : MontgInvModp_partial_solve_wit_34_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_35_non_alias : MontgInvModp_partial_solve_wit_35_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_36_in_place : MontgInvModp_partial_solve_wit_36_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_37_non_alias_pure : MontgInvModp_partial_solve_wit_37_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_37_non_alias : MontgInvModp_partial_solve_wit_37_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_38_in_place_pure : MontgInvModp_partial_solve_wit_38_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_38_in_place : MontgInvModp_partial_solve_wit_38_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_39_non_alias : MontgInvModp_partial_solve_wit_39_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_40_in_place : MontgInvModp_partial_solve_wit_40_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_41_non_alias_pure : MontgInvModp_partial_solve_wit_41_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_41_non_alias : MontgInvModp_partial_solve_wit_41_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_42_in_place_pure : MontgInvModp_partial_solve_wit_42_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_42_in_place : MontgInvModp_partial_solve_wit_42_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_43_non_alias_pure : MontgInvModp_partial_solve_wit_43_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_43_non_alias : MontgInvModp_partial_solve_wit_43_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_44_in_place_pure : MontgInvModp_partial_solve_wit_44_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_44_in_place : MontgInvModp_partial_solve_wit_44_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_45_non_alias_pure : MontgInvModp_partial_solve_wit_45_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_45_non_alias : MontgInvModp_partial_solve_wit_45_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_46_in_place_pure : MontgInvModp_partial_solve_wit_46_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_46_in_place : MontgInvModp_partial_solve_wit_46_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_47_non_alias : MontgInvModp_partial_solve_wit_47_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_48_in_place : MontgInvModp_partial_solve_wit_48_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_49_non_alias : MontgInvModp_partial_solve_wit_49_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_50_in_place : MontgInvModp_partial_solve_wit_50_in_place.
Axiom proof_of_MontgInvModp_partial_solve_wit_51_non_alias_pure : MontgInvModp_partial_solve_wit_51_non_alias_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_51_non_alias : MontgInvModp_partial_solve_wit_51_non_alias.
Axiom proof_of_MontgInvModp_partial_solve_wit_52_in_place_pure : MontgInvModp_partial_solve_wit_52_in_place_pure.
Axiom proof_of_MontgInvModp_partial_solve_wit_52_in_place : MontgInvModp_partial_solve_wit_52_in_place.
Axiom proof_of_MontgInvModp_derive_mont_in_place_by_in_place : MontgInvModp_derive_mont_in_place_by_in_place.
Axiom proof_of_MontgInvModp_derive_mont_non_alias_by_non_alias : MontgInvModp_derive_mont_non_alias_by_non_alias.

End VC_Correct.
