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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.

(*----- Function montg_inv_mod_p_ex -----*)

Definition montg_inv_mod_p_ex_entail_wit_1_1_non_alias := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_P_Z)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_u256_limbs a_pre A_non_alias )
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_inv_mod_p_ex_entail_wit_1_2_in_place := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_P_Z)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_u256_limbs a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_inv_mod_p_ex_entail_wit_2_1_non_alias := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_P_Z)) ,
  (store_fp a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (UndefStructPredu32 r_pre )
  **  (store_fp a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_inv_mod_p_ex_entail_wit_2_2_in_place := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_P_Z)) ,
  (store_fp a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (UndefStructPredu32 r_pre )
  **  (store_fp a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_inv_mod_p_ex_entail_wit_3_1_non_alias := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Ainv_non: Z) (Ainv_in: Z) (PreH1 : (0 <= Ainv_non)) (PreH2 : (Ainv_non < SM2_P_Z)) (PreH3 : ((Zmod ((A_non_alias * Ainv_non )) (SM2_P_Z)) = 1)) (PreH4 : (A_non_alias <> 0)) (PreH5 : (A_non_alias < SM2_P_Z)) ,
  (store_fp a_pre A_non_alias )
  **  (store_fp r_pre (mont_p (Ainv_non)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ (0 <= Ainv_non) ” 
  &&  “ (Ainv_non < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias * Ainv_non )) (SM2_P_Z)) = 1) ” 
  &&  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (store_u256_limbs r_pre (mont_p (Ainv_non)) )
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ (r_pre = a_pre) ” 
  &&  “ (0 <= Ainv_in) ” 
  &&  “ (Ainv_in < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_in_place * Ainv_in )) (SM2_P_Z)) = 1) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_u256_limbs r_pre (mont_p (Ainv_in)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_inv_mod_p_ex_entail_wit_3_2_in_place := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (Ainv_non: Z) (Ainv_in: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= Ainv_in)) (PreH3 : (Ainv_in < SM2_P_Z)) (PreH4 : ((Zmod ((A_in_place * Ainv_in )) (SM2_P_Z)) = 1)) (PreH5 : (r_pre = a_pre)) (PreH6 : (A_in_place <> 0)) (PreH7 : (A_in_place < SM2_P_Z)) ,
  (store_fp r_pre (mont_p (Ainv_in)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ (0 <= Ainv_non) ” 
  &&  “ (Ainv_non < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias * Ainv_non )) (SM2_P_Z)) = 1) ” 
  &&  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (store_u256_limbs r_pre (mont_p (Ainv_non)) )
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ (r_pre = a_pre) ” 
  &&  “ (0 <= Ainv_in) ” 
  &&  “ (Ainv_in < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_in_place * Ainv_in )) (SM2_P_Z)) = 1) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_u256_limbs r_pre (mont_p (Ainv_in)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_inv_mod_p_ex_return_wit_1_non_alias := 
(
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (Ainv_non_2: Z) (PreH1 : (0 <= Ainv_non_2)) (PreH2 : (Ainv_non_2 < SM2_P_Z)) (PreH3 : ((Zmod ((A_non_alias * Ainv_non_2 )) (SM2_P_Z)) = 1)) (PreH4 : (A_non_alias <> 0)) (PreH5 : (A_non_alias < SM2_P_Z)) ,
  (store_u256_limbs r_pre (mont_p (Ainv_non_2)) )
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (Ainv_non: Z) ,
  “ (0 <= Ainv_non) ” 
  &&  “ (Ainv_non < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias * Ainv_non )) (SM2_P_Z)) = 1) ”
  &&  (store_u256_limbs a_pre A_non_alias )
  **  (store_u256_limbs r_pre (mont_p (Ainv_non)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (Ainv_non_2: Z) (PreH1 : (0 <= Ainv_non_2)) (PreH2 : (Ainv_non_2 < SM2_P_Z)) (PreH3 : ((Zmod ((A_non_alias * Ainv_non_2 )) (SM2_P_Z)) = 1)) (PreH4 : (A_non_alias <> 0)) (PreH5 : (A_non_alias < SM2_P_Z)) ,
  TT && emp 
|--
  EX (Ainv_non: Z) ,
  “ ((mont_p (Ainv_non_2)) = (mont_p (Ainv_non))) ” 
  &&  “ (0 <= Ainv_non) ” 
  &&  “ (Ainv_non < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias * Ainv_non )) (SM2_P_Z)) = 1) ”
  &&  emp
).

Definition montg_inv_mod_p_ex_return_wit_2_in_place := 
(
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (Ainv_in_2: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= Ainv_in_2)) (PreH3 : (Ainv_in_2 < SM2_P_Z)) (PreH4 : ((Zmod ((A_in_place * Ainv_in_2 )) (SM2_P_Z)) = 1)) (PreH5 : (r_pre = a_pre)) (PreH6 : (A_in_place <> 0)) (PreH7 : (A_in_place < SM2_P_Z)) ,
  (store_u256_limbs r_pre (mont_p (Ainv_in_2)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (Ainv_in: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (0 <= Ainv_in) ” 
  &&  “ (Ainv_in < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_in_place * Ainv_in )) (SM2_P_Z)) = 1) ”
  &&  (store_u256_limbs r_pre (mont_p (Ainv_in)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (Ainv_in_2: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= Ainv_in_2)) (PreH3 : (Ainv_in_2 < SM2_P_Z)) (PreH4 : ((Zmod ((A_in_place * Ainv_in_2 )) (SM2_P_Z)) = 1)) (PreH5 : (r_pre = a_pre)) (PreH6 : (A_in_place <> 0)) (PreH7 : (A_in_place < SM2_P_Z)) ,
  TT && emp 
|--
  EX (Ainv_in: Z) ,
  “ ((mont_p (Ainv_in_2)) = (mont_p (Ainv_in))) ” 
  &&  “ (a_pre = a_pre) ” 
  &&  “ (0 <= Ainv_in) ” 
  &&  “ (Ainv_in < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_in_place * Ainv_in )) (SM2_P_Z)) = 1) ”
  &&  emp
).

Definition montg_inv_mod_p_ex_partial_solve_wit_1_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_P_Z)) ,
  (UndefStructPredu32 r_pre )
  **  (store_fp a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (A_non_alias <> 0) ”
.

Definition montg_inv_mod_p_ex_partial_solve_wit_1_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_P_Z)) ,
  (UndefStructPredu32 r_pre )
  **  (store_fp a_pre A_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (store_fp a_pre A_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_inv_mod_p_ex_partial_solve_wit_1_non_alias := montg_inv_mod_p_ex_partial_solve_wit_1_non_alias_pure -> montg_inv_mod_p_ex_partial_solve_wit_1_non_alias_aux.

Definition montg_inv_mod_p_ex_partial_solve_wit_2_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_P_Z)) ,
  (store_fp a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
.

Definition montg_inv_mod_p_ex_partial_solve_wit_2_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_P_Z)) ,
  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_P_Z) ”
  &&  (store_fp a_pre A_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_inv_mod_p_ex_partial_solve_wit_2_in_place := montg_inv_mod_p_ex_partial_solve_wit_2_in_place_pure -> montg_inv_mod_p_ex_partial_solve_wit_2_in_place_aux.

Definition montg_inv_mod_p_ex_derive_field_non_alias_by_non_alias := 
forall (r_pre: Z) (a_pre: Z) (PR_field_non_alias: Z) (PA_field_non_alias: Z) (A_field_non_alias: Z) ,
  “ (a_pre = PA_field_non_alias) ” 
  &&  “ (r_pre = PR_field_non_alias) ” 
  &&  “ (0 <= A_field_non_alias) ” 
  &&  “ (A_field_non_alias <> 0) ” 
  &&  “ (A_field_non_alias < SM2_P_Z) ”
  &&  (store_fp PA_field_non_alias A_field_non_alias )
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_non_alias: Z) ,
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_P_Z) ”
  &&  (store_u256_limbs a_pre A_non_alias )
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX Ainv_non,
  “ (0 <= Ainv_non) ” 
  &&  “ (Ainv_non < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_non_alias * Ainv_non )) (SM2_P_Z)) = 1) ”
  &&  (store_u256_limbs a_pre A_non_alias )
  **  (store_u256_limbs r_pre (mont_p (Ainv_non)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (EX ZI,
  “ (a_pre = PA_field_non_alias) ” 
  &&  “ (r_pre = PR_field_non_alias) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((A_field_non_alias * ZI )) (SM2_P_Z)) = 1) ”
  &&  (store_fp PA_field_non_alias A_field_non_alias )
  **  (store_fp PR_field_non_alias (mont_p (ZI)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.

Axiom proof_of_montg_inv_mod_p_ex_entail_wit_1_1_non_alias : montg_inv_mod_p_ex_entail_wit_1_1_non_alias.
Axiom proof_of_montg_inv_mod_p_ex_entail_wit_1_2_in_place : montg_inv_mod_p_ex_entail_wit_1_2_in_place.
Axiom proof_of_montg_inv_mod_p_ex_entail_wit_2_1_non_alias : montg_inv_mod_p_ex_entail_wit_2_1_non_alias.
Axiom proof_of_montg_inv_mod_p_ex_entail_wit_2_2_in_place : montg_inv_mod_p_ex_entail_wit_2_2_in_place.
Axiom proof_of_montg_inv_mod_p_ex_entail_wit_3_1_non_alias : montg_inv_mod_p_ex_entail_wit_3_1_non_alias.
Axiom proof_of_montg_inv_mod_p_ex_entail_wit_3_2_in_place : montg_inv_mod_p_ex_entail_wit_3_2_in_place.
Axiom proof_of_montg_inv_mod_p_ex_return_wit_1_non_alias : montg_inv_mod_p_ex_return_wit_1_non_alias.
Axiom proof_of_montg_inv_mod_p_ex_return_wit_2_in_place : montg_inv_mod_p_ex_return_wit_2_in_place.
Axiom proof_of_montg_inv_mod_p_ex_partial_solve_wit_1_non_alias_pure : montg_inv_mod_p_ex_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_montg_inv_mod_p_ex_partial_solve_wit_1_non_alias : montg_inv_mod_p_ex_partial_solve_wit_1_non_alias.
Axiom proof_of_montg_inv_mod_p_ex_partial_solve_wit_2_in_place_pure : montg_inv_mod_p_ex_partial_solve_wit_2_in_place_pure.
Axiom proof_of_montg_inv_mod_p_ex_partial_solve_wit_2_in_place : montg_inv_mod_p_ex_partial_solve_wit_2_in_place.
Axiom proof_of_montg_inv_mod_p_ex_derive_field_non_alias_by_non_alias : montg_inv_mod_p_ex_derive_field_non_alias_by_non_alias.

End VC_Correct.
