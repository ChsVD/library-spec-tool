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

(*----- Function get_random_u32_in_mod_n -----*)

Definition get_random_u32_in_mod_n_return_wit_1 := 
forall (k_pre: Z) (R: Z) (PreH1 : (k_pre = k_pre)) (PreH2 : (0 <= R)) (PreH3 : (R < U256_MOD)) ,
  (store_fn k_pre (Zmod (R) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  EX (K: Z) ,
  (store_fn k_pre K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition get_random_u32_in_mod_n_partial_solve_wit_1 := 
forall (k_pre: Z) ,
  (UInt64Array.undef_full &((k_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  (UInt64Array.undef_full &((k_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition get_random_u32_in_mod_n_partial_solve_wit_2_pure := 
forall (k_pre: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < U256_MOD)) ,
  (store_u256 k_pre R )
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (k_pre = k_pre) ”
.

Definition get_random_u32_in_mod_n_partial_solve_wit_2_aux := 
forall (k_pre: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < U256_MOD)) ,
  (store_u256 k_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  “ (k_pre = k_pre) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < U256_MOD) ”
  &&  (store_u256 k_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition get_random_u32_in_mod_n_partial_solve_wit_2 := get_random_u32_in_mod_n_partial_solve_wit_2_pure -> get_random_u32_in_mod_n_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_get_random_u32_in_mod_n_return_wit_1 : get_random_u32_in_mod_n_return_wit_1.
Axiom proof_of_get_random_u32_in_mod_n_partial_solve_wit_1 : get_random_u32_in_mod_n_partial_solve_wit_1.
Axiom proof_of_get_random_u32_in_mod_n_partial_solve_wit_2_pure : get_random_u32_in_mod_n_partial_solve_wit_2_pure.
Axiom proof_of_get_random_u32_in_mod_n_partial_solve_wit_2 : get_random_u32_in_mod_n_partial_solve_wit_2.

End VC_Correct.
