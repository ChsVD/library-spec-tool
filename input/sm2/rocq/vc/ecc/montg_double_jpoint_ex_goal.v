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
Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.

(*----- Function montg_double_jpoint_ex -----*)

Definition montg_double_jpoint_ex_return_wit_1_in_place := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (PreH1 : (r_pre = a_pre)) (PreH2 : (r_pre = a_pre)) ,
  (store_mont_jpoint r_pre (sm2_point_double (P_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_double (P_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_double_jpoint_ex_return_wit_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_double_jpoint_ex_partial_solve_wit_1_in_place_pure := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (PreH1 : (r_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_jpoint a_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
.

Definition montg_double_jpoint_ex_partial_solve_wit_1_in_place_aux := 
forall (r_pre: Z) (a_pre: Z) (P_in_place: ec_point) (PreH1 : (r_pre = a_pre)) ,
  (store_mont_jpoint a_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint a_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_double_jpoint_ex_partial_solve_wit_1_in_place := montg_double_jpoint_ex_partial_solve_wit_1_in_place_pure -> montg_double_jpoint_ex_partial_solve_wit_1_in_place_aux.

Definition montg_double_jpoint_ex_partial_solve_wit_2_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_non_alias: ec_point) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.

Axiom proof_of_montg_double_jpoint_ex_return_wit_1_in_place : montg_double_jpoint_ex_return_wit_1_in_place.
Axiom proof_of_montg_double_jpoint_ex_return_wit_2_non_alias : montg_double_jpoint_ex_return_wit_2_non_alias.
Axiom proof_of_montg_double_jpoint_ex_partial_solve_wit_1_in_place_pure : montg_double_jpoint_ex_partial_solve_wit_1_in_place_pure.
Axiom proof_of_montg_double_jpoint_ex_partial_solve_wit_1_in_place : montg_double_jpoint_ex_partial_solve_wit_1_in_place.
Axiom proof_of_montg_double_jpoint_ex_partial_solve_wit_2_non_alias : montg_double_jpoint_ex_partial_solve_wit_2_non_alias.

End VC_Correct.
