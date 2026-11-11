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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_facts_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import byte_memory_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_sign -----*)

Definition sm2_sign_safety_wit_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (id_len_pre <= 50)) (PreH2 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_safety_wit_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_safety_wit_3 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ~((valid_afpoint x y ))) (PreH5 : (valid_afpoint x y )) (PreH6 : (afpoint_represents x y P_generated )) (PreH7 : (valid_sm2_public_key P_generated )) (PreH8 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH9 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (id_len_pre <= 50)) (PreH11 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ False ”
.

Definition sm2_sign_safety_wit_4 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_generated )) (PreH8 : (valid_sm2_public_key P_generated )) (PreH9 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH11 : (id_len_pre <= 50)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ False ”
.

Definition sm2_sign_safety_wit_5 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_generated )) (PreH8 : (valid_sm2_public_key P_generated )) (PreH9 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH11 : (id_len_pre <= 50)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_safety_wit_6 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (id_len_pre > 50)) (PreH2 : (retval_2 = (-1))) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 1)) (PreH7 : (valid_afpoint x y )) (PreH8 : (valid_afpoint x y )) (PreH9 : (afpoint_represents x y P_generated )) (PreH10 : (valid_sm2_public_key P_generated )) (PreH11 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH12 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (id_len_pre <= 50)) (PreH14 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (UCharArray.undef_full (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_sm2_za_globals )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ False ”
.

Definition sm2_sign_safety_wit_7 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 1)) (PreH7 : (valid_afpoint x y )) (PreH8 : (valid_afpoint x y )) (PreH9 : (afpoint_represents x y P_generated )) (PreH10 : (valid_sm2_public_key P_generated )) (PreH11 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH12 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (id_len_pre <= 50)) (PreH14 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_generated P_generated (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_safety_wit_8 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 1)) (PreH7 : (valid_afpoint x y )) (PreH8 : (valid_afpoint x y )) (PreH9 : (afpoint_represents x y P_generated )) (PreH10 : (valid_sm2_public_key P_generated )) (PreH11 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH12 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (id_len_pre <= 50)) (PreH14 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_generated P_generated (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_safety_wit_9 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (id_len_pre <= 50)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 1)) (PreH8 : (valid_afpoint x y )) (PreH9 : (valid_afpoint x y )) (PreH10 : (afpoint_represents x y P_generated )) (PreH11 : (valid_sm2_public_key P_generated )) (PreH12 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH14 : (id_len_pre <= 50)) (PreH15 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))) )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_entail_wit_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (id_len_pre <= 50)) (PreH4 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
|--
  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_entail_wit_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (id_len_pre <= 50)) (PreH4 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_afpoint pubkey_pre P_generated )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_entail_wit_3 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (valid_sm2_public_key P_generated )) (PreH2 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH3 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (id_len_pre <= 50)) (PreH5 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint pubkey_pre P_generated )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  EX (y: Z)  (x: Z) ,
  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_afpoint_fields pubkey_pre x y )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_entail_wit_4 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (PreH1 : (afpoint_represents x y P_generated )) (PreH2 : (valid_sm2_public_key P_generated )) (PreH3 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (id_len_pre <= 50)) (PreH6 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_afpoint_fields pubkey_pre x y )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
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
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_entail_wit_5 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 1)) (PreH7 : (valid_afpoint x y )) (PreH8 : (valid_afpoint x y )) (PreH9 : (afpoint_represents x y P_generated )) (PreH10 : (valid_sm2_public_key P_generated )) (PreH11 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH12 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (id_len_pre <= 50)) (PreH14 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_generated P_generated (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_sm2_za_globals )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (id_len_pre <= 50) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_generated P_generated (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_return_wit_1 := 
(
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (R_2: Z) (S_2: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (sm2_signature_generated (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))))) D_generated R_2 S_2 )) (PreH3 : (retval_4 = 0)) (PreH4 : (id_len_pre <= 50)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_generated )) (PreH13 : (valid_sm2_public_key P_generated )) (PreH14 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH15 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH16 : (id_len_pre <= 50)) (PreH17 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_private_key privkey_pre D_generated )
  **  (store_sm2_signature sig_pre R_2 S_2 )
  **  (store_sm2_sign_dgst_globals )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
|--
  EX (R: Z)  (S: Z) ,
  “ (retval = 1) ” 
  &&  “ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_generated) (P_generated) (Message_generated)))) D_generated R S ) ”
  &&  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (store_sm2_signature sig_pre R S )
  **  (store_sm2_sign_globals )
) \/
(
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (R_2: Z) (S_2: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (sm2_signature_generated (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))))) D_generated R_2 S_2 )) (PreH3 : (retval_4 = 0)) (PreH4 : (id_len_pre <= 50)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_generated )) (PreH13 : (valid_sm2_public_key P_generated )) (PreH14 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH15 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH16 : (id_len_pre <= 50)) (PreH17 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_sign_dgst_globals )
  **  (store_sm3_ti )
|--
  “ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_generated) (P_generated) (Message_generated)))) D_generated R_2 S_2 ) ”
  &&  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
).

Definition sm2_sign_return_wit_1_split_goal_1 := 
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (R_2: Z) (S_2: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (sm2_signature_generated (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))))) D_generated R_2 S_2 )) (PreH3 : (retval_4 = 0)) (PreH4 : (id_len_pre <= 50)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_generated )) (PreH13 : (valid_sm2_public_key P_generated )) (PreH14 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH15 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH16 : (id_len_pre <= 50)) (PreH17 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_sign_dgst_globals )
  **  (store_sm3_ti )
|--
  “ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_generated) (P_generated) (Message_generated)))) D_generated R_2 S_2 ) ”
.

Definition sm2_sign_return_wit_1_split_goal_spatial := 
forall (id_len_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (R_2: Z) (S_2: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (sm2_signature_generated (be_u8_list_value ((sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))))) D_generated R_2 S_2 )) (PreH3 : (retval_4 = 0)) (PreH4 : (id_len_pre <= 50)) (PreH5 : (retval_3 = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (valid_afpoint x y )) (PreH11 : (valid_afpoint x y )) (PreH12 : (afpoint_represents x y P_generated )) (PreH13 : (valid_sm2_public_key P_generated )) (PreH14 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH15 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH16 : (id_len_pre <= 50)) (PreH17 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm2_sign_dgst_globals )
  **  (store_sm3_ti )
|--
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
.

Definition sm2_sign_partial_solve_wit_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (id_len_pre <= 50)) (PreH2 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
|--
  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
.

Definition sm2_sign_partial_solve_wit_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (PreH1 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
|--
  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
.

Definition sm2_sign_partial_solve_wit_3 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (PreH1 : (valid_afpoint x y )) (PreH2 : (afpoint_represents x y P_generated )) (PreH3 : (valid_sm2_public_key P_generated )) (PreH4 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH5 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH6 : (id_len_pre <= 50)) (PreH7 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_partial_solve_wit_4_pure := 
(
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_generated )) (PreH8 : (valid_sm2_public_key P_generated )) (PreH9 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH11 : (id_len_pre <= 50)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ”
) \/
(
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre <= UINT64_MAX)) (PreH3 : (id_len_pre >= 0)) (PreH4 : (msg_len_pre >= 0)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (valid_afpoint x y )) (PreH10 : (valid_afpoint x y )) (PreH11 : (afpoint_represents x y P_generated )) (PreH12 : (valid_sm2_public_key P_generated )) (PreH13 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH14 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH15 : (id_len_pre <= 50)) (PreH16 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ”
).

Definition sm2_sign_partial_solve_wit_4_pure_split_goal_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (msg_len_pre <= UINT64_MAX)) (PreH3 : (id_len_pre >= 0)) (PreH4 : (msg_len_pre >= 0)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (valid_afpoint x y )) (PreH10 : (valid_afpoint x y )) (PreH11 : (afpoint_represents x y P_generated )) (PreH12 : (valid_sm2_public_key P_generated )) (PreH13 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH14 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH15 : (id_len_pre <= 50)) (PreH16 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ”
.

Definition sm2_sign_partial_solve_wit_4_aux := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (valid_afpoint x y )) (PreH6 : (valid_afpoint x y )) (PreH7 : (afpoint_represents x y P_generated )) (PreH8 : (valid_sm2_public_key P_generated )) (PreH9 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH10 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH11 : (id_len_pre <= 50)) (PreH12 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_afpoint_fields pubkey_pre x y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (UCharArray.undef_full ( &( "ZA" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (sm2_id_digest_output_aligned (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) id_len_pre ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (UCharArray.undef_full (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_sm2_za_globals )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_partial_solve_wit_4 := sm2_sign_partial_solve_wit_4_pure -> sm2_sign_partial_solve_wit_4_aux.

Definition sm2_sign_partial_solve_wit_5_pure := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 1)) (PreH7 : (valid_afpoint x y )) (PreH8 : (valid_afpoint x y )) (PreH9 : (afpoint_represents x y P_generated )) (PreH10 : (valid_sm2_public_key P_generated )) (PreH11 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH12 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (id_len_pre <= 50)) (PreH14 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_generated P_generated (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "msg" ) )) # Ptr  |-> msg_pre)
  **  ((( &( "msg_len" ) )) # UInt64  |-> msg_len_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ”
.

Definition sm2_sign_partial_solve_wit_5_aux := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (PreH1 : (id_len_pre <= 50)) (PreH2 : (retval_2 = 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 1)) (PreH7 : (valid_afpoint x y )) (PreH8 : (valid_afpoint x y )) (PreH9 : (afpoint_represents x y P_generated )) (PreH10 : (valid_sm2_public_key P_generated )) (PreH11 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH12 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (id_len_pre <= 50)) (PreH14 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_za (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ID_generated P_generated (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UCharArray.undef_full ( &( "dgst" ) ) 32 )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (UCharArray.undef_full (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_partial_solve_wit_5 := sm2_sign_partial_solve_wit_5_pure -> sm2_sign_partial_solve_wit_5_aux.

Definition sm2_sign_partial_solve_wit_6 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_generated: ec_point) (D_generated: Z) (ID_generated: (@list Z)) (Message_generated: (@list Z)) (x: Z) (y: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (id_len_pre <= 50)) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 1)) (PreH8 : (valid_afpoint x y )) (PreH9 : (valid_afpoint x y )) (PreH10 : (afpoint_represents x y P_generated )) (PreH11 : (valid_sm2_public_key P_generated )) (PreH12 : (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) )) (PreH13 : (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) )) (PreH14 : (id_len_pre <= 50)) (PreH15 : (sm2_message_input_aligned msg_pre msg_len_pre )) ,
  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))) )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
|--
  “ (retval_3 = 0) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (valid_afpoint x y ) ” 
  &&  “ (afpoint_represents x y P_generated ) ” 
  &&  “ (valid_sm2_public_key P_generated ) ” 
  &&  “ (aligned_4 (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (aligned_4 (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_bytes (( &( "dgst" ) ) + (0 * sizeof(UCHAR))) 32 (sm3_digest_bytes ((app ((sm2_za_digest (ID_generated) (P_generated))) (Message_generated)))) )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
  **  (store_bytes (( &( "ZA" ) ) + (0 * sizeof(UCHAR))) 32 (sm2_za_digest (ID_generated) (P_generated)) )
  **  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_afpoint pubkey_pre P_generated )
.

Definition sm2_sign_derive_verifies_by_generated := 
forall (privkey_pre: Z) (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (msg_len_pre: Z) (msg_pre: Z) (sig_pre: Z) (P_verifies: ec_point) (D_verifies: Z) (ID_verifies: (@list Z)) (Message_verifies: (@list Z)) ,
  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ” 
  &&  “ (valid_sm2_keypair D_verifies P_verifies ) ”
  &&  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_sm2_public_key pubkey_pre P_verifies )
  **  (store_sm2_private_key privkey_pre D_verifies )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals )
|--
EX (Message_generated: (@list Z)) (ID_generated: (@list Z)) (D_generated: Z) (P_generated: ec_point) ,
  (“ (id_len_pre <= 50) ” 
  &&  “ (sm2_message_input_aligned msg_pre msg_len_pre ) ”
  &&  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_globals ))
  **
  ((EX R_2 S_2 retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_generated) (P_generated) (Message_generated)))) D_generated R_2 S_2 ) ”
  &&  (store_bytes msg_pre msg_len_pre Message_generated )
  **  (store_bytes id_pre id_len_pre ID_generated )
  **  (store_sm2_public_key pubkey_pre P_generated )
  **  (store_sm2_private_key privkey_pre D_generated )
  **  (store_sm2_signature sig_pre R_2 S_2 )
  **  (store_sm2_sign_globals ))
  -*
  (EX R S retval,
  “ (retval = 1) ” 
  &&  “ (sm2_signature_generated (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) D_verifies R S ) ” 
  &&  “ (sm2_signature_verifies (be_u8_list_value ((sm2_message_digest (ID_verifies) (P_verifies) (Message_verifies)))) P_verifies R S ) ”
  &&  (store_bytes msg_pre msg_len_pre Message_verifies )
  **  (store_bytes id_pre id_len_pre ID_verifies )
  **  (store_sm2_public_key pubkey_pre P_verifies )
  **  (store_sm2_private_key privkey_pre D_verifies )
  **  (store_sm2_signature sig_pre R S )
  **  (store_sm2_sign_globals )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_point_facts_Strategy_Correct.
Include byte_memory_views_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_sign_safety_wit_1 : sm2_sign_safety_wit_1.
Axiom proof_of_sm2_sign_safety_wit_2 : sm2_sign_safety_wit_2.
Axiom proof_of_sm2_sign_safety_wit_3 : sm2_sign_safety_wit_3.
Axiom proof_of_sm2_sign_safety_wit_4 : sm2_sign_safety_wit_4.
Axiom proof_of_sm2_sign_safety_wit_5 : sm2_sign_safety_wit_5.
Axiom proof_of_sm2_sign_safety_wit_6 : sm2_sign_safety_wit_6.
Axiom proof_of_sm2_sign_safety_wit_7 : sm2_sign_safety_wit_7.
Axiom proof_of_sm2_sign_safety_wit_8 : sm2_sign_safety_wit_8.
Axiom proof_of_sm2_sign_safety_wit_9 : sm2_sign_safety_wit_9.
Axiom proof_of_sm2_sign_entail_wit_1 : sm2_sign_entail_wit_1.
Axiom proof_of_sm2_sign_entail_wit_2 : sm2_sign_entail_wit_2.
Axiom proof_of_sm2_sign_entail_wit_3 : sm2_sign_entail_wit_3.
Axiom proof_of_sm2_sign_entail_wit_4 : sm2_sign_entail_wit_4.
Axiom proof_of_sm2_sign_entail_wit_5 : sm2_sign_entail_wit_5.
Axiom proof_of_sm2_sign_return_wit_1 : sm2_sign_return_wit_1.
Axiom proof_of_sm2_sign_partial_solve_wit_1 : sm2_sign_partial_solve_wit_1.
Axiom proof_of_sm2_sign_partial_solve_wit_2 : sm2_sign_partial_solve_wit_2.
Axiom proof_of_sm2_sign_partial_solve_wit_3 : sm2_sign_partial_solve_wit_3.
Axiom proof_of_sm2_sign_partial_solve_wit_4_pure : sm2_sign_partial_solve_wit_4_pure.
Axiom proof_of_sm2_sign_partial_solve_wit_4 : sm2_sign_partial_solve_wit_4.
Axiom proof_of_sm2_sign_partial_solve_wit_5_pure : sm2_sign_partial_solve_wit_5_pure.
Axiom proof_of_sm2_sign_partial_solve_wit_5 : sm2_sign_partial_solve_wit_5.
Axiom proof_of_sm2_sign_partial_solve_wit_6 : sm2_sign_partial_solve_wit_6.
Axiom proof_of_sm2_sign_derive_verifies_by_generated : sm2_sign_derive_verifies_by_generated.

End VC_Correct.
