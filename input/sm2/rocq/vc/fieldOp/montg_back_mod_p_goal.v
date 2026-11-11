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
From SimpleC.EE.Applications_human.sm2.vc.fieldOp Require Import montg_back_mod_p_def.
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

(*----- Function montg_back_mod_p -----*)

Definition montg_back_mod_p_safety_wit_1_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_back_mod_p_safety_wit_2_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_back_mod_p_safety_wit_3_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_back_mod_p_safety_wit_4_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_back_mod_p_safety_wit_5_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_back_mod_p_safety_wit_6_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_back_mod_p_safety_wit_7_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_back_mod_p_safety_wit_8_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_back_mod_p_return_wit_1_in_place := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= Zout_2)) (PreH3 : (Zout_2 < SM2_P_Z)) (PreH4 : ((Zout_2 * U256_MOD ) = ((A_in_place * 1 ) + (K_2 * SM2_P_Z ) ))) (PreH5 : (result_pre = a_pre)) ,
  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = (A_in_place + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (result_pre = a_pre)) (PreH2 : (0 <= Zout_2)) (PreH3 : (Zout_2 < SM2_P_Z)) (PreH4 : ((Zout_2 * U256_MOD ) = ((A_in_place * 1 ) + (K_2 * SM2_P_Z ) ))) (PreH5 : (result_pre = a_pre)) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ (a_pre = a_pre) ” 
  &&  “ ((Zout_2 * U256_MOD ) = (A_in_place + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition montg_back_mod_p_return_wit_2_non_alias := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((A_non_alias * 1 ) + (K_2 * SM2_P_Z ) ))) ,
  (store_u256 a_pre A_non_alias )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = (A_non_alias + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((A_non_alias * 1 ) + (K_2 * SM2_P_Z ) ))) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ ((Zout_2 * U256_MOD ) = (A_non_alias + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition montg_back_mod_p_partial_solve_wit_1_in_place_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
).

Definition montg_back_mod_p_partial_solve_wit_1_in_place_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
.

Definition montg_back_mod_p_partial_solve_wit_1_in_place_aux := 
forall (result_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (result_pre = a_pre)) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = a_pre) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ” 
  &&  “ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_in_place )
  **  (store_u256 ( &( "ONE" ) ) 1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_back_mod_p_partial_solve_wit_1_in_place := montg_back_mod_p_partial_solve_wit_1_in_place_pure -> montg_back_mod_p_partial_solve_wit_1_in_place_aux.

Definition montg_back_mod_p_partial_solve_wit_2_non_alias_pure := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
) \/
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
).

Definition montg_back_mod_p_partial_solve_wit_2_non_alias_pure_split_goal_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
.

Definition montg_back_mod_p_partial_solve_wit_2_non_alias_aux := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (UInt64Array.full &(( &( "ONE" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_u256 ( &( "ONE" ) ) 1 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_back_mod_p_partial_solve_wit_2_non_alias := montg_back_mod_p_partial_solve_wit_2_non_alias_pure -> montg_back_mod_p_partial_solve_wit_2_non_alias_aux.

Definition montg_back_mod_p_derive_regular_in_place_by_in_place := 
forall (result_pre: Z) (a_pre: Z) (A_regular_in_place: Z) ,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= A_regular_in_place) ” 
  &&  “ (A_regular_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_regular_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_in_place: Z) ,
  (“ (result_pre = a_pre) ”
  &&  (store_u256 a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Zout,
  “ (result_pre = a_pre) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = (A_in_place + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (“ (result_pre = a_pre) ”
  &&  (store_fp result_pre A_regular_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Definition montg_back_mod_p_derive_regular_non_alias_by_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_regular_non_alias: Z) ,
  “ (0 <= A_regular_non_alias) ” 
  &&  “ (A_regular_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre (mont_p (A_regular_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_non_alias: Z) ,
  ((store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Zout,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = (A_non_alias + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  ((store_fp a_pre (mont_p (A_regular_non_alias)) )
  **  (store_fp result_pre A_regular_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_montg_back_mod_p_safety_wit_1_non_alias : montg_back_mod_p_safety_wit_1_non_alias.
Axiom proof_of_montg_back_mod_p_safety_wit_2_in_place : montg_back_mod_p_safety_wit_2_in_place.
Axiom proof_of_montg_back_mod_p_safety_wit_3_non_alias : montg_back_mod_p_safety_wit_3_non_alias.
Axiom proof_of_montg_back_mod_p_safety_wit_4_in_place : montg_back_mod_p_safety_wit_4_in_place.
Axiom proof_of_montg_back_mod_p_safety_wit_5_non_alias : montg_back_mod_p_safety_wit_5_non_alias.
Axiom proof_of_montg_back_mod_p_safety_wit_6_in_place : montg_back_mod_p_safety_wit_6_in_place.
Axiom proof_of_montg_back_mod_p_safety_wit_7_non_alias : montg_back_mod_p_safety_wit_7_non_alias.
Axiom proof_of_montg_back_mod_p_safety_wit_8_in_place : montg_back_mod_p_safety_wit_8_in_place.
Axiom proof_of_montg_back_mod_p_return_wit_1_in_place : montg_back_mod_p_return_wit_1_in_place.
Axiom proof_of_montg_back_mod_p_return_wit_2_non_alias : montg_back_mod_p_return_wit_2_non_alias.
Axiom proof_of_montg_back_mod_p_partial_solve_wit_1_in_place_pure : montg_back_mod_p_partial_solve_wit_1_in_place_pure.
Axiom proof_of_montg_back_mod_p_partial_solve_wit_1_in_place : montg_back_mod_p_partial_solve_wit_1_in_place.
Axiom proof_of_montg_back_mod_p_partial_solve_wit_2_non_alias_pure : montg_back_mod_p_partial_solve_wit_2_non_alias_pure.
Axiom proof_of_montg_back_mod_p_partial_solve_wit_2_non_alias : montg_back_mod_p_partial_solve_wit_2_non_alias.
Axiom proof_of_montg_back_mod_p_derive_regular_in_place_by_in_place : montg_back_mod_p_derive_regular_in_place_by_in_place.
Axiom proof_of_montg_back_mod_p_derive_regular_non_alias_by_non_alias : montg_back_mod_p_derive_regular_non_alias_by_non_alias.

End VC_Correct.
