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
Require Import
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.

(*----- Function montg_inv_mod_n_ex -----*)

Definition montg_inv_mod_n_ex_entail_wit_1_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_N_Z)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_u256_limbs a_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_fn a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (store_fn a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition montg_inv_mod_n_ex_entail_wit_1_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_N_Z)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_u256_limbs a_pre A_non_alias )
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_fn a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (store_fn a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition montg_inv_mod_n_ex_entail_wit_2_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_N_Z)) ,
  (store_fn a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_fn a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (UndefStructPredu32 r_pre )
  **  (store_fn a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition montg_inv_mod_n_ex_entail_wit_2_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_N_Z)) ,
  (store_fn a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full r_pre 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_fn a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (UndefStructPredu32 r_pre )
  **  (store_fn a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition montg_inv_mod_n_ex_entail_wit_3_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (z_call_non: Z) (k_call_non: Z) (z_call_in: Z) (k_call_in: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= z_call_in)) (PreH3 : (z_call_in < SM2_N_Z)) (PreH4 : ((A_in_place * z_call_in ) = (U256_MOD + (k_call_in * SM2_N_Z ) ))) (PreH5 : (r_pre = a_pre)) (PreH6 : (A_in_place <> 0)) (PreH7 : (A_in_place < SM2_N_Z)) ,
  (store_fn r_pre z_call_in )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (0 <= z_call_in) ” 
  &&  “ (z_call_in < SM2_N_Z) ” 
  &&  “ ((A_in_place * z_call_in ) = (U256_MOD + (k_call_in * SM2_N_Z ) )) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_u256_limbs r_pre z_call_in )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ (0 <= z_call_non) ” 
  &&  “ (z_call_non < SM2_N_Z) ” 
  &&  “ ((A_non_alias * z_call_non ) = (U256_MOD + (k_call_non * SM2_N_Z ) )) ” 
  &&  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (store_u256_limbs r_pre z_call_non )
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_inv_mod_n_ex_entail_wit_3_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (A_in_place: Z) (z_call_non: Z) (k_call_non: Z) (z_call_in: Z) (k_call_in: Z) (PreH1 : (0 <= z_call_non)) (PreH2 : (z_call_non < SM2_N_Z)) (PreH3 : ((A_non_alias * z_call_non ) = (U256_MOD + (k_call_non * SM2_N_Z ) ))) (PreH4 : (A_non_alias <> 0)) (PreH5 : (A_non_alias < SM2_N_Z)) ,
  (store_fn a_pre A_non_alias )
  **  (store_fn r_pre z_call_non )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ (r_pre = a_pre) ” 
  &&  “ (0 <= z_call_in) ” 
  &&  “ (z_call_in < SM2_N_Z) ” 
  &&  “ ((A_in_place * z_call_in ) = (U256_MOD + (k_call_in * SM2_N_Z ) )) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_u256_limbs r_pre z_call_in )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ (0 <= z_call_non) ” 
  &&  “ (z_call_non < SM2_N_Z) ” 
  &&  “ ((A_non_alias * z_call_non ) = (U256_MOD + (k_call_non * SM2_N_Z ) )) ” 
  &&  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (store_u256_limbs r_pre z_call_non )
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_inv_mod_n_ex_return_wit_1_in_place := 
(
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (z_call_in: Z) (k_call_in: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= z_call_in)) (PreH3 : (z_call_in < SM2_N_Z)) (PreH4 : ((A_in_place * z_call_in ) = (U256_MOD + (k_call_in * SM2_N_Z ) ))) (PreH5 : (r_pre = a_pre)) (PreH6 : (A_in_place <> 0)) (PreH7 : (A_in_place < SM2_N_Z)) ,
  (store_u256_limbs r_pre z_call_in )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (K1in: Z)  (Zin: Z) ,
  “ (r_pre = a_pre) ” 
  &&  “ (0 <= Zin) ” 
  &&  “ (Zin < SM2_N_Z) ” 
  &&  “ ((A_in_place * Zin ) = (U256_MOD + (K1in * SM2_N_Z ) )) ”
  &&  (store_u256_limbs r_pre Zin )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (z_call_in: Z) (k_call_in: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (0 <= z_call_in)) (PreH3 : (z_call_in < SM2_N_Z)) (PreH4 : ((A_in_place * z_call_in ) = (U256_MOD + (k_call_in * SM2_N_Z ) ))) (PreH5 : (r_pre = a_pre)) (PreH6 : (A_in_place <> 0)) (PreH7 : (A_in_place < SM2_N_Z)) ,
  TT && emp 
|--
  EX (K1in: Z) ,
  “ (a_pre = a_pre) ” 
  &&  “ ((A_in_place * z_call_in ) = (U256_MOD + (K1in * SM2_N_Z ) )) ”
  &&  emp
).

Definition montg_inv_mod_n_ex_return_wit_2_non_alias := 
(
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (z_call_non: Z) (k_call_non: Z) (PreH1 : (0 <= z_call_non)) (PreH2 : (z_call_non < SM2_N_Z)) (PreH3 : ((A_non_alias * z_call_non ) = (U256_MOD + (k_call_non * SM2_N_Z ) ))) (PreH4 : (A_non_alias <> 0)) (PreH5 : (A_non_alias < SM2_N_Z)) ,
  (store_u256_limbs r_pre z_call_non )
  **  (store_u256_limbs a_pre A_non_alias )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (K1non: Z)  (Znon: Z) ,
  “ (0 <= Znon) ” 
  &&  “ (Znon < SM2_N_Z) ” 
  &&  “ ((A_non_alias * Znon ) = (U256_MOD + (K1non * SM2_N_Z ) )) ”
  &&  (store_u256_limbs a_pre A_non_alias )
  **  (store_u256_limbs r_pre Znon )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (A_non_alias: Z) (z_call_non: Z) (k_call_non: Z) (PreH1 : (0 <= z_call_non)) (PreH2 : (z_call_non < SM2_N_Z)) (PreH3 : ((A_non_alias * z_call_non ) = (U256_MOD + (k_call_non * SM2_N_Z ) ))) (PreH4 : (A_non_alias <> 0)) (PreH5 : (A_non_alias < SM2_N_Z)) ,
  TT && emp 
|--
  EX (K1non: Z) ,
  “ ((A_non_alias * z_call_non ) = (U256_MOD + (K1non * SM2_N_Z ) )) ”
  &&  emp
).

Definition montg_inv_mod_n_ex_partial_solve_wit_1_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_N_Z)) ,
  (store_fn a_pre A_in_place )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ”
.

Definition montg_inv_mod_n_ex_partial_solve_wit_1_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (A_in_place: Z) (PreH1 : (r_pre = a_pre)) (PreH2 : (A_in_place <> 0)) (PreH3 : (A_in_place < SM2_N_Z)) ,
  (store_fn a_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (r_pre = a_pre) ” 
  &&  “ (A_in_place <> 0) ” 
  &&  “ (A_in_place < SM2_N_Z) ”
  &&  (store_fn a_pre A_in_place )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition montg_inv_mod_n_ex_partial_solve_wit_1_in_place := montg_inv_mod_n_ex_partial_solve_wit_1_in_place_pure -> montg_inv_mod_n_ex_partial_solve_wit_1_in_place_aux.

Definition montg_inv_mod_n_ex_partial_solve_wit_2_non_alias_pure := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_N_Z)) ,
  (UndefStructPredu32 r_pre )
  **  (store_fn a_pre A_non_alias )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (A_non_alias <> 0) ”
.

Definition montg_inv_mod_n_ex_partial_solve_wit_2_non_alias_aux := 
forall (r_pre: Z) (a_pre: Z) (A_non_alias: Z) (PreH1 : (A_non_alias <> 0)) (PreH2 : (A_non_alias < SM2_N_Z)) ,
  (UndefStructPredu32 r_pre )
  **  (store_fn a_pre A_non_alias )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias <> 0) ” 
  &&  “ (A_non_alias < SM2_N_Z) ”
  &&  (store_fn a_pre A_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition montg_inv_mod_n_ex_partial_solve_wit_2_non_alias := montg_inv_mod_n_ex_partial_solve_wit_2_non_alias_pure -> montg_inv_mod_n_ex_partial_solve_wit_2_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.

Axiom proof_of_montg_inv_mod_n_ex_entail_wit_1_1_in_place : montg_inv_mod_n_ex_entail_wit_1_1_in_place.
Axiom proof_of_montg_inv_mod_n_ex_entail_wit_1_2_non_alias : montg_inv_mod_n_ex_entail_wit_1_2_non_alias.
Axiom proof_of_montg_inv_mod_n_ex_entail_wit_2_1_in_place : montg_inv_mod_n_ex_entail_wit_2_1_in_place.
Axiom proof_of_montg_inv_mod_n_ex_entail_wit_2_2_non_alias : montg_inv_mod_n_ex_entail_wit_2_2_non_alias.
Axiom proof_of_montg_inv_mod_n_ex_entail_wit_3_1_in_place : montg_inv_mod_n_ex_entail_wit_3_1_in_place.
Axiom proof_of_montg_inv_mod_n_ex_entail_wit_3_2_non_alias : montg_inv_mod_n_ex_entail_wit_3_2_non_alias.
Axiom proof_of_montg_inv_mod_n_ex_return_wit_1_in_place : montg_inv_mod_n_ex_return_wit_1_in_place.
Axiom proof_of_montg_inv_mod_n_ex_return_wit_2_non_alias : montg_inv_mod_n_ex_return_wit_2_non_alias.
Axiom proof_of_montg_inv_mod_n_ex_partial_solve_wit_1_in_place_pure : montg_inv_mod_n_ex_partial_solve_wit_1_in_place_pure.
Axiom proof_of_montg_inv_mod_n_ex_partial_solve_wit_1_in_place : montg_inv_mod_n_ex_partial_solve_wit_1_in_place.
Axiom proof_of_montg_inv_mod_n_ex_partial_solve_wit_2_non_alias_pure : montg_inv_mod_n_ex_partial_solve_wit_2_non_alias_pure.
Axiom proof_of_montg_inv_mod_n_ex_partial_solve_wit_2_non_alias : montg_inv_mod_n_ex_partial_solve_wit_2_non_alias.

End VC_Correct.
