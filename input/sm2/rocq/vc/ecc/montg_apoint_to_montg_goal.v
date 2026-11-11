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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.

(*----- Function montg_apoint_to_montg -----*)

Definition montg_apoint_to_montg_safety_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_P_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_P_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") Y_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") X_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((result_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((result_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_apoint_to_montg_return_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_P_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_P_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") Y_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") X_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
|--
  “ (1 = 1) ”
  &&  (store_afpoint_fields a_pre X_non_alias Y_non_alias )
  **  (store_mont_afpoint_coords result_pre X_non_alias Y_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_apoint_to_montg_partial_solve_wit_1 := 
forall (result_pre: Z) (a_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  (store_afpoint_fields a_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_apoint_to_montg_partial_solve_wit_2 := 
forall (result_pre: Z) (a_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_P_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_P_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") X_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") X_non_alias )
  **  (store_fp &((result_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
.

Definition montg_apoint_to_montg_derive_point_non_alias_by_non_alias := 
forall (result_pre: Z) (a_pre: Z) (P_point_non_alias: ec_point) ,
  (store_afpoint a_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) ,
  ((store_afpoint_fields a_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  ((EX retval_2,
  “ (retval_2 = 1) ”
  &&  (store_afpoint_fields a_pre X_non_alias Y_non_alias )
  **  (store_mont_afpoint_coords result_pre X_non_alias Y_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  -*
  (EX retval,
  “ (retval = 1) ”
  &&  (store_afpoint a_pre P_point_non_alias )
  **  (store_mont_afpoint result_pre P_point_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
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
Include ecc_representation_Strategy_Correct.

Axiom proof_of_montg_apoint_to_montg_safety_wit_1 : montg_apoint_to_montg_safety_wit_1.
Axiom proof_of_montg_apoint_to_montg_return_wit_1 : montg_apoint_to_montg_return_wit_1.
Axiom proof_of_montg_apoint_to_montg_partial_solve_wit_1 : montg_apoint_to_montg_partial_solve_wit_1.
Axiom proof_of_montg_apoint_to_montg_partial_solve_wit_2 : montg_apoint_to_montg_partial_solve_wit_2.
Axiom proof_of_montg_apoint_to_montg_derive_point_non_alias_by_non_alias : montg_apoint_to_montg_derive_point_non_alias_by_non_alias.
Axiom proof_of_montg_to_mod_p_derive_mont_non_alias_by_non_alias : montg_to_mod_p_derive_mont_non_alias_by_non_alias.

End VC_Correct.
