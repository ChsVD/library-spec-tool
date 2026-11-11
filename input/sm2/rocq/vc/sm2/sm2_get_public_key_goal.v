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
      SimpleC.EE.Applications_human.sm2.lib.sm3_def.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_ecc_const_table.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_protocol.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_get_public_key -----*)

Definition sm2_get_public_key_entail_wit_1 := 
forall (pubkey_pre: Z) (privkey_pre: Z) (D: Z) ,
  (UndefStructPredJPoint ( &( "rst_jacobian" ) ) )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_private_key privkey_pre D )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
|--
  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredJPoint ( &( "rst_jacobian" ) ) )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_private_key privkey_pre D )
  **  (UndefStructPredAFPoint pubkey_pre )
.

Definition sm2_get_public_key_entail_wit_2 := 
forall (pubkey_pre: Z) (privkey_pre: Z) (D: Z) ,
  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredJPoint ( &( "rst_jacobian" ) ) )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_private_key privkey_pre D )
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  (UndefStructPredu32 &(( &( "rst_jacobian" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "rst_jacobian" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "rst_jacobian" ) )->ₛ "x") )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_private_key privkey_pre D )
  **  (UndefStructPredAFPoint pubkey_pre )
.

Definition sm2_get_public_key_return_wit_1 := 
(
forall (pubkey_pre: Z) (privkey_pre: Z) (D: Z) (PreH1 : (valid_sm2_private_key D )) ,
  (store_afpoint pubkey_pre (sm2_point_mul (D) (SM2_G_POINT)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_sm2_base_point_table )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
|--
  (store_sm2_private_key privkey_pre D )
  **  (store_sm2_public_key pubkey_pre (sm2_point_mul (D) (SM2_G_POINT)) )
  **  (store_sm2_get_public_key_globals )
) \/
(
forall (D: Z) (PreH1 : (valid_sm2_private_key D )) ,
  TT && emp 
|--
  “ (valid_sm2_public_key (sm2_point_mul (D) (SM2_G_POINT)) ) ”
  &&  emp
).

Definition sm2_get_public_key_return_wit_1_split_goal_1 := 
forall (D: Z) (PreH1 : (valid_sm2_private_key D )) ,
  (valid_sm2_public_key (sm2_point_mul (D) (SM2_G_POINT)) )
.

Definition sm2_get_public_key_partial_solve_wit_1 := 
forall (pubkey_pre: Z) (privkey_pre: Z) (D: Z) ,
  (UndefStructPredu32 &(( &( "rst_jacobian" ) )->ₛ "z") )
  **  (UndefStructPredu32 &(( &( "rst_jacobian" ) )->ₛ "y") )
  **  (UndefStructPredu32 &(( &( "rst_jacobian" ) )->ₛ "x") )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (store_sm2_private_key privkey_pre D )
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ (valid_sm2_private_key D ) ”
  &&  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (UInt64Array.undef_full &(( &( "rst_jacobian" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rst_jacobian" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rst_jacobian" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  (UndefStructPredAFPoint pubkey_pre )
.

Definition sm2_get_public_key_partial_solve_wit_2 := 
forall (pubkey_pre: Z) (privkey_pre: Z) (D: Z) (PreH1 : (valid_sm2_private_key D )) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_jpoint_with_canonical_infinity ( &( "rst_jacobian" ) ) (sm2_point_mul (D) (SM2_G_POINT)) )
  **  (store_sm2_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ (valid_sm2_private_key D ) ”
  &&  (store_jpoint_with_canonical_infinity ( &( "rst_jacobian" ) ) (sm2_point_mul (D) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full &((pubkey_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((pubkey_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_sm2_base_point_table )
  **  (store_jpoint_zero )
  **  (store_sm2_inv2p )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_get_public_key_entail_wit_1 : sm2_get_public_key_entail_wit_1.
Axiom proof_of_sm2_get_public_key_entail_wit_2 : sm2_get_public_key_entail_wit_2.
Axiom proof_of_sm2_get_public_key_return_wit_1 : sm2_get_public_key_return_wit_1.
Axiom proof_of_sm2_get_public_key_partial_solve_wit_1 : sm2_get_public_key_partial_solve_wit_1.
Axiom proof_of_sm2_get_public_key_partial_solve_wit_2 : sm2_get_public_key_partial_solve_wit_2.

End VC_Correct.
