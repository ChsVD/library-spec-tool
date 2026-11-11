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
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_verify -----*)

Definition sm2_verify_safety_wit_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (id_len_pre <= 50)) (PreH2 : (P_verifies <> ECInfinity)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_safety_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (P_verifies <> ECInfinity)) (PreH4 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_safety_wit_3 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (id_len_pre <= 50)) (PreH4 : (P_verifies <> ECInfinity)) (PreH5 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_safety_wit_4 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (PreH1 : (id_len_pre > 50)) (PreH2 : (retval = (-1))) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (P_verifies <> ECInfinity)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (UCharArray.undef_full (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_sm2_za_globals )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
|--
  “ False ”
.

Definition sm2_verify_safety_wit_5 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval = 0)) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (P_verifies <> ECInfinity)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_verifies P_verifies (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_safety_wit_6 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval = 0)) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (P_verifies <> ECInfinity)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_verifies P_verifies (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_safety_wit_7 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (id_len_pre <= 50)) (PreH3 : (retval = 0)) (PreH4 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH6 : (id_len_pre <= 50)) (PreH7 : (P_verifies <> ECInfinity)) (PreH8 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))) )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_verify_entail_wit_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (id_len_pre <= 50)) (PreH4 : (P_verifies <> ECInfinity)) (PreH5 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
|--
  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
.

Definition sm2_verify_entail_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval = 0)) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (P_verifies <> ECInfinity)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_verifies P_verifies (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_sm2_za_globals )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
|--
  “ (id_len_pre <= 50) ” 
  &&  “ (retval = 0) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_verifies P_verifies (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
.

Definition sm2_verify_return_wit_1 := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies )) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_bytes id_pre id_len_pre ID_verifies )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies ) ”
  &&  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
) \/
(
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies )) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_verify_dgst_globals )
  **  (store_sm3_ti )
|--
  “ (sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies ) ”
  &&  (store_sm3_ti )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
).

Definition sm2_verify_return_wit_1_split_goal_1 := 
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies )) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_verify_dgst_globals )
  **  (store_sm3_ti )
|--
  “ (sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies ) ”
.

Definition sm2_verify_return_wit_1_split_goal_spatial := 
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies )) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_verify_dgst_globals )
  **  (store_sm3_ti )
|--
  (store_sm3_ti )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
.

Definition sm2_verify_return_wit_2 := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ~((sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies ))) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_bytes id_pre id_len_pre ID_verifies )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
) \/
(
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ~((sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies ))) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_verify_dgst_globals )
  **  (store_sm3_ti )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm3_ti )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
).

Definition sm2_verify_return_wit_2_split_goal_1 := 
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ~((sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies ))) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_verify_dgst_globals )
  **  (store_sm3_ti )
|--
  “ ~((sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies )) ”
.

Definition sm2_verify_return_wit_2_split_goal_spatial := 
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ~((sm2_signature_verifies (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))))) P_verifies SigR_verifies SigS_verifies ))) (PreH5 : (retval_3 = 0)) (PreH6 : (id_len_pre <= 50)) (PreH7 : (retval_2 = 0)) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (P_verifies <> ECInfinity)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_verify_dgst_globals )
  **  (store_sm3_ti )
|--
  (store_sm3_ti )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
.

Definition sm2_verify_partial_solve_wit_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (id_len_pre <= 50)) (PreH2 : (P_verifies <> ECInfinity)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
|--
  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
.

Definition sm2_verify_partial_solve_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (P_verifies <> ECInfinity)) (PreH4 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
|--
  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )
.

Definition sm2_verify_partial_solve_wit_3_pure := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (id_len_pre <= 50)) (PreH4 : (P_verifies <> ECInfinity)) (PreH5 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ”
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre <= UINT64_MAX)) (PreH3 : (id_len_pre >= 0)) (PreH4 : (msg_len_pre >= 0)) (PreH5 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH6 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH7 : (id_len_pre <= 50)) (PreH8 : (P_verifies <> ECInfinity)) (PreH9 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ”
).

Definition sm2_verify_partial_solve_wit_3_pure_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre <= UINT64_MAX)) (PreH3 : (id_len_pre >= 0)) (PreH4 : (msg_len_pre >= 0)) (PreH5 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH6 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH7 : (id_len_pre <= 50)) (PreH8 : (P_verifies <> ECInfinity)) (PreH9 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ”
.

Definition sm2_verify_partial_solve_wit_3_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (PreH1 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (id_len_pre <= 50)) (PreH4 : (P_verifies <> ECInfinity)) (PreH5 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (UCharArray.undef_full (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_sm2_za_globals )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
.

Definition sm2_verify_partial_solve_wit_3 := sm2_verify_partial_solve_wit_3_pure -> sm2_verify_partial_solve_wit_3_aux.

Definition sm2_verify_partial_solve_wit_4_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval = 0)) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (P_verifies <> ECInfinity)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_verifies P_verifies (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
|--
  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ”
.

Definition sm2_verify_partial_solve_wit_4_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval = 0)) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (P_verifies <> ECInfinity)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_verifies P_verifies (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
|--
  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (retval = 0) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (UCharArray.undef_full (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
.

Definition sm2_verify_partial_solve_wit_4 := sm2_verify_partial_solve_wit_4_pure -> sm2_verify_partial_solve_wit_4_aux.

Definition sm2_verify_partial_solve_wit_5_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (id_len_pre <= 50)) (PreH3 : (retval = 0)) (PreH4 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH6 : (id_len_pre <= 50)) (PreH7 : (P_verifies <> ECInfinity)) (PreH8 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))) )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
|--
  “ (P_verifies <> ECInfinity) ”
.

Definition sm2_verify_partial_solve_wit_5_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_verifies: Z) (SigR_verifies: Z) (P_verifies: ec_point) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (id_len_pre <= 50)) (PreH3 : (retval = 0)) (PreH4 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH6 : (id_len_pre <= 50)) (PreH7 : (P_verifies <> ECInfinity)) (PreH8 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))) )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_jpoint_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_h )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
|--
  “ (P_verifies <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (retval = 0) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_verifies) (P_verifies))) (Message_verifies)))) )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_dgst_globals )
  **  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_verifies) (P_verifies)) )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_bytes id_pre id_len_pre ID_verifies )
.

Definition sm2_verify_partial_solve_wit_5 := sm2_verify_partial_solve_wit_5_pure -> sm2_verify_partial_solve_wit_5_aux.

Definition sm2_verify_derive_generated_by_verifies := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (SigS_generated: Z) (SigR_generated: Z) (P_generated: ec_point) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (D_2: Z) ,
  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_sm2_signature sig_pre SigR_generated SigS_generated )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_verify_globals )
|--
EX (Message_verifies: (@list Z)) (ID_verifies: (@list Z)) (P_verifies: ec_point) (SigR_verifies: Z) (SigS_verifies: Z) ,
  (“ (id_len_pre <= 50) ” 
  &&  “ (P_verifies <> ECInfinity) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals ))
  **
  (((EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies ) ”
  &&  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies SigR_verifies SigS_verifies )) ”
  &&  (store_sm2_signature sig_pre SigR_verifies SigS_verifies )
  **  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_afpoint pubkey_pre P_verifies )
  **  (store_sm2_verify_globals )))
  -*
  ((EX D retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_sm2_keypair D P_generated ) ” 
  &&  “ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_generated) (P_generated) (Message_generated)))) D SigR_generated SigS_generated ) ”
  &&  (store_sm2_signature sig_pre SigR_generated SigS_generated )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_verify_globals ))
  ||
  (EX retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~(exists (D_2: Z) , ((valid_sm2_keypair D_2 P_generated ) /\ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_generated) (P_generated) (Message_generated)))) D_2 SigR_generated SigS_generated ))) ”
  &&  (store_sm2_signature sig_pre SigR_generated SigS_generated )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_verify_globals ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include byte_memory_views_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_verify_safety_wit_1 : sm2_verify_safety_wit_1.
Axiom proof_of_sm2_verify_safety_wit_2 : sm2_verify_safety_wit_2.
Axiom proof_of_sm2_verify_safety_wit_3 : sm2_verify_safety_wit_3.
Axiom proof_of_sm2_verify_safety_wit_4 : sm2_verify_safety_wit_4.
Axiom proof_of_sm2_verify_safety_wit_5 : sm2_verify_safety_wit_5.
Axiom proof_of_sm2_verify_safety_wit_6 : sm2_verify_safety_wit_6.
Axiom proof_of_sm2_verify_safety_wit_7 : sm2_verify_safety_wit_7.
Axiom proof_of_sm2_verify_entail_wit_1 : sm2_verify_entail_wit_1.
Axiom proof_of_sm2_verify_entail_wit_2 : sm2_verify_entail_wit_2.
Axiom proof_of_sm2_verify_return_wit_1 : sm2_verify_return_wit_1.
Axiom proof_of_sm2_verify_return_wit_2 : sm2_verify_return_wit_2.
Axiom proof_of_sm2_verify_partial_solve_wit_1 : sm2_verify_partial_solve_wit_1.
Axiom proof_of_sm2_verify_partial_solve_wit_2 : sm2_verify_partial_solve_wit_2.
Axiom proof_of_sm2_verify_partial_solve_wit_3_pure : sm2_verify_partial_solve_wit_3_pure.
Axiom proof_of_sm2_verify_partial_solve_wit_3 : sm2_verify_partial_solve_wit_3.
Axiom proof_of_sm2_verify_partial_solve_wit_4_pure : sm2_verify_partial_solve_wit_4_pure.
Axiom proof_of_sm2_verify_partial_solve_wit_4 : sm2_verify_partial_solve_wit_4.
Axiom proof_of_sm2_verify_partial_solve_wit_5_pure : sm2_verify_partial_solve_wit_5_pure.
Axiom proof_of_sm2_verify_partial_solve_wit_5 : sm2_verify_partial_solve_wit_5.
Axiom proof_of_sm2_verify_derive_generated_by_verifies : sm2_verify_derive_generated_by_verifies.

End VC_Correct.
