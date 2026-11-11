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

(*----- Function montg_to_mod_p -----*)

Definition montg_to_mod_p_entail_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_u256 ( &( "SM2_H" ) ) SM2_H_Z )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_to_mod_p_return_wit_1 := 
(
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((A_non_alias * SM2_H_Z ) + (K_2 * SM2_P_Z ) ))) ,
  (store_u256 a_pre A_non_alias )
  **  (store_u256 ( &( "SM2_H" ) ) SM2_H_Z )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_non_alias * SM2_H_Z ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (A_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((A_non_alias * SM2_H_Z ) + (K_2 * SM2_P_Z ) ))) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ ((Zout_2 * U256_MOD ) = ((A_non_alias * SM2_H_Z ) + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition montg_to_mod_p_partial_solve_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (A_non_alias: Z) ,
  (store_u256 ( &( "SM2_H" ) ) SM2_H_Z )
  **  (store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_u256 a_pre A_non_alias )
  **  (store_u256 ( &( "SM2_H" ) ) SM2_H_Z )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_to_mod_p_derive_mont_non_alias_by_non_alias := 
forall (result_pre: Z) (a_pre: Z) (A_mont_non_alias: Z) ,
  (store_fp a_pre A_mont_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (A_non_alias: Z) ,
  ((store_u256 a_pre A_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX K Zout,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((A_non_alias * SM2_H_Z ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 a_pre A_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  ((store_fp a_pre A_mont_non_alias )
  **  (store_fp result_pre (mont_p (A_mont_non_alias)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_montg_to_mod_p_entail_wit_1 : montg_to_mod_p_entail_wit_1.
Axiom proof_of_montg_to_mod_p_return_wit_1 : montg_to_mod_p_return_wit_1.
Axiom proof_of_montg_to_mod_p_partial_solve_wit_1 : montg_to_mod_p_partial_solve_wit_1.
Axiom proof_of_montg_to_mod_p_derive_mont_non_alias_by_non_alias : montg_to_mod_p_derive_mont_non_alias_by_non_alias.

End VC_Correct.
