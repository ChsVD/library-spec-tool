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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_sign_dgst_def.
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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_sign_dgst -----*)

Definition sm2_sign_dgst_safety_wit_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_3 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_4 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_5 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_6 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_7 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_8 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_9 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (S = 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval = 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_10 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (S <> 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval <> 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_11 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (K = 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_12 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 <> 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_13 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_14 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_15 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0)) (PreH5 : (retval_4 = 0)) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 <= 1)) (PreH8 : (retval_4 = 1)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0)) (PreH10 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH11 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH12 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH14 : (K < SM2_N_Z)) (PreH15 : (0 <= K)) (PreH16 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH17 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH18 : (retval_3 = 1)) (PreH19 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH20 : (0 <= retval_2)) (PreH21 : (retval_2 <= 1)) (PreH22 : (retval_2 = 0)) (PreH23 : (K <> 0)) (PreH24 : (K < SM2_N_Z)) (PreH25 : (0 <= K)) (PreH26 : (0 <= retval)) (PreH27 : (retval <= 1)) (PreH28 : (retval = 1)) (PreH29 : (S = 0)) (PreH30 : (0 <= R)) (PreH31 : (R < SM2_N_Z)) (PreH32 : (0 <= S)) (PreH33 : (S < SM2_N_Z)) (PreH34 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH35 : (retval <> 0)) (PreH36 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_16 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH5 : (retval_4 = 0)) (PreH6 : (0 <= retval_4)) (PreH7 : (retval_4 <= 1)) (PreH8 : (retval_4 = 1)) (PreH9 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0)) (PreH10 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH11 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH12 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH14 : (K < SM2_N_Z)) (PreH15 : (0 <= K)) (PreH16 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH17 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH18 : (retval_3 = 1)) (PreH19 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH20 : (0 <= retval_2)) (PreH21 : (retval_2 <= 1)) (PreH22 : (retval_2 = 0)) (PreH23 : (K <> 0)) (PreH24 : (K < SM2_N_Z)) (PreH25 : (0 <= K)) (PreH26 : (0 <= retval)) (PreH27 : (retval <= 1)) (PreH28 : (retval = 1)) (PreH29 : (S = 0)) (PreH30 : (0 <= R)) (PreH31 : (R < SM2_N_Z)) (PreH32 : (0 <= S)) (PreH33 : (S < SM2_N_Z)) (PreH34 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH35 : (retval <> 0)) (PreH36 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_17 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_18 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 0)) (PreH5 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH6 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH7 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH8 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH10 : (K < SM2_N_Z)) (PreH11 : (0 <= K)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH14 : (retval_3 = 1)) (PreH15 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (K <> 0)) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (S = 0)) (PreH26 : (0 <= R)) (PreH27 : (R < SM2_N_Z)) (PreH28 : (0 <= S)) (PreH29 : (S < SM2_N_Z)) (PreH30 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH31 : (retval <> 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_19 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition sm2_sign_dgst_safety_wit_20 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_21 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm2_sign_dgst_safety_wit_22 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") 1 4 )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm2_sign_dgst_safety_wit_23 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") 1 4 )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_24 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sm2_sign_dgst_safety_wit_25 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_26 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition sm2_sign_dgst_safety_wit_27 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_sign_dgst_safety_wit_28 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (xs: (@list Z)) (xs_2: (@list Z)) (PreH1 : ((u64_list_value (xs_2)) = R)) (PreH2 : (u64_list_bounded xs_2 )) (PreH3 : ((Zlength (xs_2)) = 4)) (PreH4 : ((u64_list_value (xs)) = S)) (PreH5 : (u64_list_bounded xs )) (PreH6 : ((Zlength (xs)) = 4)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (S <> 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval = 0)) ,
  (UInt64Array.full &((sig_pre)  # "SM2SIG" ->ₛ "s" .ₛ "v") 4 xs )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 xs )
  **  (UInt64Array.full &((sig_pre)  # "SM2SIG" ->ₛ "r" .ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 xs_2 )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm2_sign_dgst_entail_wit_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_sm2_sign_dgst_globals )
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
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_dgst_entail_wit_2 := 
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (PreH1 : (( &( "e" ) ) = ( &( "e" ) ))) ,
  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
|--
  EX (S: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ”
  &&  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (store_u256 ( &( "s" ) ) S )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (D: Z) (DigestBytes: (@list Z)) ,
  TT && emp 
|--
  “ (((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) )) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) < SM2_N_Z) ” 
  &&  “ (0 <= (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) )))) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) < SM2_N_Z) ” 
  &&  “ (0 <= (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) )))) ”
  &&  emp
).

Definition sm2_sign_dgst_entail_wit_2_split_goal_1 := 
forall (D: Z) (DigestBytes: (@list Z)) ,
  (((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) ))
.

Definition sm2_sign_dgst_entail_wit_2_split_goal_2 := 
  ((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) < SM2_N_Z)
.

Definition sm2_sign_dgst_entail_wit_2_split_goal_3 := 
  (0 <= (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))))
.

Definition sm2_sign_dgst_entail_wit_2_split_goal_4 := 
  ((u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))) < SM2_N_Z)
.

Definition sm2_sign_dgst_entail_wit_2_split_goal_5 := 
  (0 <= (u64_list_value (((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ))))
.

Definition sm2_sign_dgst_entail_wit_3_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (S = 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval_2 = 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (S <> 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_3_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (S <> 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval = 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (S <> 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_4_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (S = 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval <> 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_4_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (S <> 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval_2 <> 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_5_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (K = 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_3 = 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_5_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_6_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (K = 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 <> 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (K = 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_6_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_3 <> 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (K = 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_7 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (0 = 0)) (PreH3 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (K <> 0)) (PreH8 : (K < SM2_N_Z)) (PreH9 : (0 <= K)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 1)) (PreH13 : (S = 0)) (PreH14 : (0 <= R)) (PreH15 : (R < SM2_N_Z)) (PreH16 : (0 <= S)) (PreH17 : (S < SM2_N_Z)) (PreH18 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH19 : (retval <> 0)) (PreH20 : (retval_2 = 0)) ,
  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_u256_limbs (&(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) RX )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_3 = 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_entail_wit_8 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (K <> 0)) (PreH7 : (K < SM2_N_Z)) (PreH8 : (0 <= K)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (S = 0)) (PreH13 : (0 <= R)) (PreH14 : (R < SM2_N_Z)) (PreH15 : (0 <= S)) (PreH16 : (S < SM2_N_Z)) (PreH17 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH18 : (retval <> 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_fn ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_entail_wit_9_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_entail_wit_9_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_6: Z) (PreH1 : (retval_6 = 0)) (PreH2 : (0 <= retval_6)) (PreH3 : (retval_6 <= 1)) (PreH4 : (retval_6 = 1)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  EX (retval_5: Z) ,
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_entail_wit_10_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH6 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH7 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH8 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH10 : (K < SM2_N_Z)) (PreH11 : (0 <= K)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH14 : (retval_3 = 1)) (PreH15 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (K <> 0)) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (S = 0)) (PreH26 : (0 <= R)) (PreH27 : (R < SM2_N_Z)) (PreH28 : (0 <= S)) (PreH29 : (S < SM2_N_Z)) (PreH30 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH31 : (retval <> 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n ))
.

Definition sm2_sign_dgst_entail_wit_10_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0)) (PreH6 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH7 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH8 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH10 : (K < SM2_N_Z)) (PreH11 : (0 <= K)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH14 : (retval_3 = 1)) (PreH15 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (K <> 0)) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (S = 0)) (PreH26 : (0 <= R)) (PreH27 : (R < SM2_N_Z)) (PreH28 : (0 <= S)) (PreH29 : (S < SM2_N_Z)) (PreH30 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH31 : (retval <> 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_entail_wit_10_3 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_5: Z) (retval_7: Z) (PreH1 : (retval_7 <> 0)) (PreH2 : (0 <= retval_7)) (PreH3 : (retval_7 <= 1)) (PreH4 : (retval_7 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= retval_5)) (PreH8 : (retval_5 <= 1)) (PreH9 : (retval_5 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  (EX (retval_4: Z) ,
  “ (retval_4 <> 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n ))
  ||
  (EX (retval_6: Z) ,
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n ))
.

Definition sm2_sign_dgst_entail_wit_10_4 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 <> 0)) (PreH2 : (0 <= retval_6)) (PreH3 : (retval_6 <= 1)) (PreH4 : (retval_6 = 1)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0)) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= retval_5)) (PreH8 : (retval_5 <= 1)) (PreH9 : (retval_5 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_6 <> 0) ” 
  &&  “ (0 <= retval_6) ” 
  &&  “ (retval_6 <= 1) ” 
  &&  “ (retval_6 = 1) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_entail_wit_11_1 := 
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_N_Z)) (PreH3 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH4 : (valid_sm2_private_key D )) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S_2 = 0)) (PreH35 : (0 <= R_2)) (PreH36 : (R_2 < SM2_N_Z)) (PreH37 : (0 <= S_2)) (PreH38 : (S_2 < SM2_N_Z)) (PreH39 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_fn ( &( "k_subtract_rda" ) ) (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn ( &( "s" ) ) (Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
|--
  EX (S: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ”
  &&  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (store_u256 ( &( "s" ) ) S )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH3 : ((Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH4 : (0 <= (Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH5 : (0 <= Ainv)) (PreH6 : (Ainv < SM2_N_Z)) (PreH7 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH8 : (valid_sm2_private_key D )) (PreH9 : (retval_5 = 0)) (PreH10 : (0 <= retval_5)) (PreH11 : (retval_5 <= 1)) (PreH12 : (retval_5 = 0)) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH14 : (retval_4 = 0)) (PreH15 : (0 <= retval_4)) (PreH16 : (retval_4 <= 1)) (PreH17 : (retval_4 = 0)) (PreH18 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH19 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH20 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH21 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH23 : (K < SM2_N_Z)) (PreH24 : (0 <= K)) (PreH25 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH26 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH27 : (retval_3 = 1)) (PreH28 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (K <> 0)) (PreH33 : (K < SM2_N_Z)) (PreH34 : (0 <= K)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (retval = 1)) (PreH38 : (S_2 = 0)) (PreH39 : (0 <= R_2)) (PreH40 : (R_2 < SM2_N_Z)) (PreH41 : (0 <= S_2)) (PreH42 : (S_2 < SM2_N_Z)) (PreH43 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH44 : (retval <> 0)) (PreH45 : (retval_2 = 0)) ,
  TT && emp 
|--
  “ (((Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) (Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) )) ”
  &&  emp
).

Definition sm2_sign_dgst_entail_wit_11_1_split_goal_1 := 
forall (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH3 : ((Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH4 : (0 <= (Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH5 : (0 <= Ainv)) (PreH6 : (Ainv < SM2_N_Z)) (PreH7 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH8 : (valid_sm2_private_key D )) (PreH9 : (retval_5 = 0)) (PreH10 : (0 <= retval_5)) (PreH11 : (retval_5 <= 1)) (PreH12 : (retval_5 = 0)) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH14 : (retval_4 = 0)) (PreH15 : (0 <= retval_4)) (PreH16 : (retval_4 <= 1)) (PreH17 : (retval_4 = 0)) (PreH18 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH19 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH20 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH21 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH23 : (K < SM2_N_Z)) (PreH24 : (0 <= K)) (PreH25 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH26 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH27 : (retval_3 = 1)) (PreH28 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH29 : (0 <= retval_2)) (PreH30 : (retval_2 <= 1)) (PreH31 : (retval_2 = 0)) (PreH32 : (K <> 0)) (PreH33 : (K < SM2_N_Z)) (PreH34 : (0 <= K)) (PreH35 : (0 <= retval)) (PreH36 : (retval <= 1)) (PreH37 : (retval = 1)) (PreH38 : (S_2 = 0)) (PreH39 : (0 <= R_2)) (PreH40 : (R_2 < SM2_N_Z)) (PreH41 : (0 <= S_2)) (PreH42 : (S_2 < SM2_N_Z)) (PreH43 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH44 : (retval <> 0)) (PreH45 : (retval_2 = 0)) ,
  (((Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) (Zmod ((Ainv * (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )) (SM2_N_Z)) ))
.

Definition sm2_sign_dgst_entail_wit_11_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (K = 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S_2 = 0)) (PreH11 : (0 <= R_2)) (PreH12 : (R_2 < SM2_N_Z)) (PreH13 : (0 <= S_2)) (PreH14 : (S_2 < SM2_N_Z)) (PreH15 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 <> 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R_2 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (S: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ”
  &&  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (store_u256 ( &( "s" ) ) S )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_11_3 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0)) (PreH6 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH7 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH8 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH10 : (K < SM2_N_Z)) (PreH11 : (0 <= K)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH14 : (retval_3 = 1)) (PreH15 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (K <> 0)) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (S_2 = 0)) (PreH26 : (0 <= R_2)) (PreH27 : (R_2 < SM2_N_Z)) (PreH28 : (0 <= S_2)) (PreH29 : (S_2 < SM2_N_Z)) (PreH30 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH31 : (retval <> 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  EX (S: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ”
  &&  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (store_u256 ( &( "s" ) ) S )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_11_4 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 <> 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 1)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) = 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S_2 = 0)) (PreH31 : (0 <= R_2)) (PreH32 : (R_2 < SM2_N_Z)) (PreH33 : (0 <= S_2)) (PreH34 : (S_2 < SM2_N_Z)) (PreH35 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S_2 )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  EX (S: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ”
  &&  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (store_u256 ( &( "s" ) ) S )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_12 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (S <> 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval = 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (S <> 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval = 0) ”
  &&  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "s") )
  **  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "r") )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_entail_wit_13 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (S <> 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval = 0)) ,
  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "s") )
  **  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "r") )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (xs_2: (@list Z))  (xs: (@list Z)) ,
  “ ((u64_list_value (xs_2)) = R) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ ((u64_list_value (xs)) = S) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (S <> 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval = 0) ”
  &&  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "s") )
  **  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "r") )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_return_wit_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S_2: Z) (R_2: Z) (retval: Z) (xs: (@list Z)) (xs_2: (@list Z)) (PreH1 : ((u64_list_value (xs_2)) = R_2)) (PreH2 : (u64_list_bounded xs_2 )) (PreH3 : ((Zlength (xs_2)) = 4)) (PreH4 : ((u64_list_value (xs)) = S_2)) (PreH5 : (u64_list_bounded xs )) (PreH6 : ((Zlength (xs)) = 4)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (S_2 <> 0)) (PreH11 : (0 <= R_2)) (PreH12 : (R_2 < SM2_N_Z)) (PreH13 : (0 <= S_2)) (PreH14 : (S_2 < SM2_N_Z)) (PreH15 : ((S_2 <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R_2 S_2 ))) (PreH16 : (retval = 0)) ,
  (UInt64Array.full &((sig_pre)  # "SM2SIG" ->ₛ "s" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((sig_pre)  # "SM2SIG" ->ₛ "r" .ₛ "v") 4 xs_2 )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (R: Z)  (S: Z) ,
  “ (1 = 1) ” 
  &&  “ (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ) ”
  &&  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_sm2_signature sig_pre R S )
  **  (store_sm2_sign_dgst_globals )
.

Definition sm2_sign_dgst_partial_solve_wit_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
|--
  (store_bytes dgst_pre 32 DigestBytes )
  **  (UndefStructPredu32 ( &( "e" ) ) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_dgst_partial_solve_wit_2_pure := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
|--
  “ (( &( "e" ) ) = ( &( "e" ) )) ”
.

Definition sm2_sign_dgst_partial_solve_wit_2_aux := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) ,
  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
|--
  “ (( &( "e" ) ) = ( &( "e" ) )) ”
  &&  (store_u256 ( &( "e" ) ) (be_u8_list_value (DigestBytes)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
  **  (UndefStructPredAFPoint ( &( "rand_AFPoint" ) ) )
  **  (UndefStructPredJPoint ( &( "rand_JPoint" ) ) )
  **  (UndefStructPredu32 ( &( "k_subtract_rda" ) ) )
  **  (UndefStructPredu32 ( &( "inversion_da_and_1" ) ) )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "k" ) ) )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 ((make_record_u32 ((repeat_Z (0) (4)))).(u32_v) ) )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
.

Definition sm2_sign_dgst_partial_solve_wit_2 := sm2_sign_dgst_partial_solve_wit_2_pure -> sm2_sign_dgst_partial_solve_wit_2_aux.

Definition sm2_sign_dgst_partial_solve_wit_3 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : (0 <= S)) (PreH4 : (S < SM2_N_Z)) (PreH5 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) ,
  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (store_u256 ( &( "s" ) ) S )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ”
  &&  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_partial_solve_wit_4 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (S = 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval <> 0)) ,
  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ”
  &&  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_partial_solve_wit_5 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (S = 0)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : (0 <= S)) (PreH8 : (S < SM2_N_Z)) (PreH9 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH10 : (retval <> 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_partial_solve_wit_6 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "k" ) ) K )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_7_pure := 
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 = 0) ” 
  &&  “ ((&(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) <> 0) ”
) \/
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((&(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) <> 0) ”
).

Definition sm2_sign_dgst_partial_solve_wit_7_pure_split_goal_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((&(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) <> 0) ”
.

Definition sm2_sign_dgst_partial_solve_wit_7_aux := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (K <> 0)) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (S = 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 = 0) ” 
  &&  “ ((&(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) <> 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (UInt64Array.undef_full (&(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_7 := sm2_sign_dgst_partial_solve_wit_7_pure -> sm2_sign_dgst_partial_solve_wit_7_aux.

Definition sm2_sign_dgst_partial_solve_wit_8_pure := 
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (0 = 0)) (PreH3 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (K <> 0)) (PreH8 : (K < SM2_N_Z)) (PreH9 : (0 <= K)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 1)) (PreH13 : (S = 0)) (PreH14 : (0 <= R)) (PreH15 : (R < SM2_N_Z)) (PreH16 : (0 <= S)) (PreH17 : (S < SM2_N_Z)) (PreH18 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH19 : (retval <> 0)) (PreH20 : (retval_2 = 0)) ,
  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "tmp" ) ) <> &(( &( "rand_AFPoint" ) )->ₛ "x")) ”
) \/
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (K <> 0)) (PreH7 : (K < SM2_N_Z)) (PreH8 : (0 <= K)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (S = 0)) (PreH13 : (0 <= R)) (PreH14 : (R < SM2_N_Z)) (PreH15 : (0 <= S)) (PreH16 : (S < SM2_N_Z)) (PreH17 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH18 : (retval <> 0)) (PreH19 : (retval_2 = 0)) ,
  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "tmp" ) ) <> &(( &( "rand_AFPoint" ) )->ₛ "x")) ”
).

Definition sm2_sign_dgst_partial_solve_wit_8_pure_split_goal_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (K <> 0)) (PreH7 : (K < SM2_N_Z)) (PreH8 : (0 <= K)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (S = 0)) (PreH13 : (0 <= R)) (PreH14 : (R < SM2_N_Z)) (PreH15 : (0 <= S)) (PreH16 : (S < SM2_N_Z)) (PreH17 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH18 : (retval <> 0)) (PreH19 : (retval_2 = 0)) ,
  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "tmp" ) ) <> &(( &( "rand_AFPoint" ) )->ₛ "x")) ”
.

Definition sm2_sign_dgst_partial_solve_wit_8_aux := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (0 = 0)) (PreH3 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (K <> 0)) (PreH8 : (K < SM2_N_Z)) (PreH9 : (0 <= K)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 1)) (PreH13 : (S = 0)) (PreH14 : (0 <= R)) (PreH15 : (R < SM2_N_Z)) (PreH16 : (0 <= S)) (PreH17 : (S < SM2_N_Z)) (PreH18 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH19 : (retval <> 0)) (PreH20 : (retval_2 = 0)) ,
  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "tmp" ) ) <> &(( &( "rand_AFPoint" ) )->ₛ "x")) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_8 := sm2_sign_dgst_partial_solve_wit_8_pure -> sm2_sign_dgst_partial_solve_wit_8_aux.

Definition sm2_sign_dgst_partial_solve_wit_9 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (K <> 0)) (PreH7 : (K < SM2_N_Z)) (PreH8 : (0 <= K)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (S = 0)) (PreH13 : (0 <= R)) (PreH14 : (R < SM2_N_Z)) (PreH15 : (0 <= S)) (PreH16 : (S < SM2_N_Z)) (PreH17 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH18 : (retval <> 0)) (PreH19 : (retval_2 = 0)) ,
  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_fn ( &( "tmp" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) R )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_fn ( &( "tmp" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "r" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_10 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (K <> 0)) (PreH7 : (K < SM2_N_Z)) (PreH8 : (0 <= K)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 1)) (PreH12 : (S = 0)) (PreH13 : (0 <= R)) (PreH14 : (R < SM2_N_Z)) (PreH15 : (0 <= S)) (PreH16 : (S < SM2_N_Z)) (PreH17 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH18 : (retval <> 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_fn ( &( "tmp" ) ) (Zmod (RX) (SM2_N_Z)) )
  **  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn ( &( "k" ) ) K )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_11 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (PreH1 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH3 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH4 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH5 : (K < SM2_N_Z)) (PreH6 : (0 <= K)) (PreH7 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH8 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH9 : (retval_3 = 1)) (PreH10 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH11 : (0 <= retval_2)) (PreH12 : (retval_2 <= 1)) (PreH13 : (retval_2 = 0)) (PreH14 : (K <> 0)) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : (0 <= retval)) (PreH18 : (retval <= 1)) (PreH19 : (retval = 1)) (PreH20 : (S = 0)) (PreH21 : (0 <= R)) (PreH22 : (R < SM2_N_Z)) (PreH23 : (0 <= S)) (PreH24 : (S < SM2_N_Z)) (PreH25 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH26 : (retval <> 0)) (PreH27 : (retval_2 = 0)) ,
  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_12 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 0)) (PreH5 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH6 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH7 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH8 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH10 : (K < SM2_N_Z)) (PreH11 : (0 <= K)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH14 : (retval_3 = 1)) (PreH15 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (K <> 0)) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (S = 0)) (PreH26 : (0 <= R)) (PreH27 : (R < SM2_N_Z)) (PreH28 : (0 <= S)) (PreH29 : (S < SM2_N_Z)) (PreH30 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH31 : (retval <> 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_13 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 1)) (PreH5 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0)) (PreH6 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH7 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH8 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH9 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH10 : (K < SM2_N_Z)) (PreH11 : (0 <= K)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH14 : (retval_3 = 1)) (PreH15 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH16 : (0 <= retval_2)) (PreH17 : (retval_2 <= 1)) (PreH18 : (retval_2 = 0)) (PreH19 : (K <> 0)) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : (0 <= retval)) (PreH23 : (retval <= 1)) (PreH24 : (retval = 1)) (PreH25 : (S = 0)) (PreH26 : (0 <= R)) (PreH27 : (R < SM2_N_Z)) (PreH28 : (0 <= S)) (PreH29 : (S < SM2_N_Z)) (PreH30 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH31 : (retval <> 0)) (PreH32 : (retval_2 = 0)) ,
  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) = 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_14 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") 1 4 )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_15 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") 1 4 )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_16 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") (1 + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "inversion_da_and_1" ) )->ₛ "v") 2 (1 + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_17 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |->_)
  **  (UInt64Array.undef_missing_i &(( &( "inversion_da_and_1" ) )->ₛ "v") 3 ((1 + 1 ) + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_18_pure := 
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) )) ” 
  &&  “ (0 <= (u256_of_limbs (1) (0) (0) (0))) ” 
  &&  “ ((u256_of_limbs (1) (0) (0) (0)) < SM2_N_Z) ” 
  &&  “ (1 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ”
) \/
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (1 < U64_MOD) ” 
  &&  “ ((u256_of_limbs (1) (0) (0) (0)) < SM2_N_Z) ” 
  &&  “ (0 <= (u256_of_limbs (1) (0) (0) (0))) ”
).

Definition sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 < U64_MOD) ”
.

Definition sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_2 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 < U64_MOD) ”
.

Definition sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_3 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 < U64_MOD) ”
.

Definition sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_4 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (1 < U64_MOD) ”
.

Definition sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_5 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((u256_of_limbs (1) (0) (0) (0)) < SM2_N_Z) ”
.

Definition sm2_sign_dgst_partial_solve_wit_18_pure_split_goal_6 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (1 <= UINT64_MAX)) (PreH2 : (0 <= UINT64_MAX)) (PreH3 : (1 >= 0)) (PreH4 : (0 >= 0)) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= (u256_of_limbs (1) (0) (0) (0))) ”
.

Definition sm2_sign_dgst_partial_solve_wit_18_aux := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = 0)) (PreH2 : (0 <= retval_5)) (PreH3 : (retval_5 <= 1)) (PreH4 : (retval_5 = 0)) (PreH5 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH6 : (retval_4 = 0)) (PreH7 : (0 <= retval_4)) (PreH8 : (retval_4 <= 1)) (PreH9 : (retval_4 = 0)) (PreH10 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH11 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH12 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH13 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH15 : (K < SM2_N_Z)) (PreH16 : (0 <= K)) (PreH17 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH19 : (retval_3 = 1)) (PreH20 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH21 : (0 <= retval_2)) (PreH22 : (retval_2 <= 1)) (PreH23 : (retval_2 = 0)) (PreH24 : (K <> 0)) (PreH25 : (K < SM2_N_Z)) (PreH26 : (0 <= K)) (PreH27 : (0 <= retval)) (PreH28 : (retval <= 1)) (PreH29 : (retval = 1)) (PreH30 : (S = 0)) (PreH31 : (0 <= R)) (PreH32 : (R < SM2_N_Z)) (PreH33 : (0 <= S)) (PreH34 : (S < SM2_N_Z)) (PreH35 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH36 : (retval <> 0)) (PreH37 : (retval_2 = 0)) ,
  (UInt64Array.undef_seg &(( &( "inversion_da_and_1" ) )->ₛ "v") (((1 + 1 ) + 1 ) + 1 ) 4 )
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (((&(( &( "inversion_da_and_1" ) )->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> 1)
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_sm2_n )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) )) ” 
  &&  “ (0 <= (u256_of_limbs (1) (0) (0) (0))) ” 
  &&  “ ((u256_of_limbs (1) (0) (0) (0)) < SM2_N_Z) ” 
  &&  “ (1 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (0 < U64_MOD) ” 
  &&  “ (valid_sm2_private_key D ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "inversion_da_and_1" ) ) (u256_of_limbs (1) (0) (0) (0)) )
  **  (store_sm2_n )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
.

Definition sm2_sign_dgst_partial_solve_wit_18 := sm2_sign_dgst_partial_solve_wit_18_pure -> sm2_sign_dgst_partial_solve_wit_18_aux.

Definition sm2_sign_dgst_partial_solve_wit_19_pure := 
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) ))) (PreH2 : (valid_sm2_private_key D )) (PreH3 : (retval_5 = 0)) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= 1)) (PreH6 : (retval_5 = 0)) (PreH7 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH8 : (retval_4 = 0)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (retval_4 = 0)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH13 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH15 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH17 : (K < SM2_N_Z)) (PreH18 : (0 <= K)) (PreH19 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH20 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH21 : (retval_3 = 1)) (PreH22 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (K <> 0)) (PreH27 : (K < SM2_N_Z)) (PreH28 : (0 <= K)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (retval = 1)) (PreH32 : (S = 0)) (PreH33 : (0 <= R)) (PreH34 : (R < SM2_N_Z)) (PreH35 : (0 <= S)) (PreH36 : (S < SM2_N_Z)) (PreH37 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH38 : (retval <> 0)) (PreH39 : (retval_2 = 0)) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "inversion_da_and_1" ) ) (Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) )) ” 
  &&  “ ((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) <> 0) ”
) \/
(
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (valid_sm2_private_key D )) (PreH2 : (retval_5 = 0)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (retval_5 = 0)) (PreH6 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH7 : (retval_4 = 0)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (retval_4 = 0)) (PreH11 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH12 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH14 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH15 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH16 : (K < SM2_N_Z)) (PreH17 : (0 <= K)) (PreH18 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH19 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH20 : (retval_3 = 1)) (PreH21 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH22 : (0 <= retval_2)) (PreH23 : (retval_2 <= 1)) (PreH24 : (retval_2 = 0)) (PreH25 : (K <> 0)) (PreH26 : (K < SM2_N_Z)) (PreH27 : (0 <= K)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (S = 0)) (PreH32 : (0 <= R)) (PreH33 : (R < SM2_N_Z)) (PreH34 : (0 <= S)) (PreH35 : (S < SM2_N_Z)) (PreH36 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH37 : (retval <> 0)) (PreH38 : (retval_2 = 0)) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "inversion_da_and_1" ) ) (Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) <> 0) ”
).

Definition sm2_sign_dgst_partial_solve_wit_19_pure_split_goal_1 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (valid_sm2_private_key D )) (PreH2 : (retval_5 = 0)) (PreH3 : (0 <= retval_5)) (PreH4 : (retval_5 <= 1)) (PreH5 : (retval_5 = 0)) (PreH6 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH7 : (retval_4 = 0)) (PreH8 : (0 <= retval_4)) (PreH9 : (retval_4 <= 1)) (PreH10 : (retval_4 = 0)) (PreH11 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH12 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH13 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH14 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH15 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH16 : (K < SM2_N_Z)) (PreH17 : (0 <= K)) (PreH18 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH19 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH20 : (retval_3 = 1)) (PreH21 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH22 : (0 <= retval_2)) (PreH23 : (retval_2 <= 1)) (PreH24 : (retval_2 = 0)) (PreH25 : (K <> 0)) (PreH26 : (K < SM2_N_Z)) (PreH27 : (0 <= K)) (PreH28 : (0 <= retval)) (PreH29 : (retval <= 1)) (PreH30 : (retval = 1)) (PreH31 : (S = 0)) (PreH32 : (0 <= R)) (PreH33 : (R < SM2_N_Z)) (PreH34 : (0 <= S)) (PreH35 : (S < SM2_N_Z)) (PreH36 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH37 : (retval <> 0)) (PreH38 : (retval_2 = 0)) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "inversion_da_and_1" ) ) (Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ ((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) <> 0) ”
.

Definition sm2_sign_dgst_partial_solve_wit_19_aux := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) ))) (PreH2 : (valid_sm2_private_key D )) (PreH3 : (retval_5 = 0)) (PreH4 : (0 <= retval_5)) (PreH5 : (retval_5 <= 1)) (PreH6 : (retval_5 = 0)) (PreH7 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH8 : (retval_4 = 0)) (PreH9 : (0 <= retval_4)) (PreH10 : (retval_4 <= 1)) (PreH11 : (retval_4 = 0)) (PreH12 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH13 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH14 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH15 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH17 : (K < SM2_N_Z)) (PreH18 : (0 <= K)) (PreH19 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH20 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH21 : (retval_3 = 1)) (PreH22 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH23 : (0 <= retval_2)) (PreH24 : (retval_2 <= 1)) (PreH25 : (retval_2 = 0)) (PreH26 : (K <> 0)) (PreH27 : (K < SM2_N_Z)) (PreH28 : (0 <= K)) (PreH29 : (0 <= retval)) (PreH30 : (retval <= 1)) (PreH31 : (retval = 1)) (PreH32 : (S = 0)) (PreH33 : (0 <= R)) (PreH34 : (R < SM2_N_Z)) (PreH35 : (0 <= S)) (PreH36 : (S < SM2_N_Z)) (PreH37 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH38 : (retval <> 0)) (PreH39 : (retval_2 = 0)) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "inversion_da_and_1" ) ) (Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_sm2_rhon )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
|--
  “ (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) )) ” 
  &&  “ ((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ (valid_sm2_private_key D ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "inversion_da_and_1" ) ) (Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
.

Definition sm2_sign_dgst_partial_solve_wit_19 := sm2_sign_dgst_partial_solve_wit_19_pure -> sm2_sign_dgst_partial_solve_wit_19_aux.

Definition sm2_sign_dgst_partial_solve_wit_20 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : (( &( "inversion_da_and_1" ) ) = ( &( "inversion_da_and_1" ) ))) (PreH2 : (0 <= Ainv)) (PreH3 : (Ainv < SM2_N_Z)) (PreH4 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH5 : (valid_sm2_private_key D )) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= retval_5)) (PreH8 : (retval_5 <= 1)) (PreH9 : (retval_5 = 0)) (PreH10 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= retval_4)) (PreH13 : (retval_4 <= 1)) (PreH14 : (retval_4 = 0)) (PreH15 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH16 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH17 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH18 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH19 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH23 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH24 : (retval_3 = 1)) (PreH25 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (K <> 0)) (PreH30 : (K < SM2_N_Z)) (PreH31 : (0 <= K)) (PreH32 : (0 <= retval)) (PreH33 : (retval <= 1)) (PreH34 : (retval = 1)) (PreH35 : (S = 0)) (PreH36 : (0 <= R)) (PreH37 : (R < SM2_N_Z)) (PreH38 : (0 <= S)) (PreH39 : (S < SM2_N_Z)) (PreH40 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH41 : (retval <> 0)) (PreH42 : (retval_2 = 0)) ,
  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_nh )
|--
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_N_Z) ” 
  &&  “ ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1) ” 
  &&  “ (valid_sm2_private_key D ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
.

Definition sm2_sign_dgst_partial_solve_wit_21_pure := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_N_Z)) (PreH3 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH4 : (valid_sm2_private_key D )) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "k_subtract_rda" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  ((( &( "sig" ) )) # Ptr  |-> sig_pre)
  **  ((( &( "dgst" ) )) # Ptr  |-> dgst_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "k_subtract_rda" ) ) = ( &( "k_subtract_rda" ) )) ”
.

Definition sm2_sign_dgst_partial_solve_wit_21_aux := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : (0 <= Ainv)) (PreH2 : (Ainv < SM2_N_Z)) (PreH3 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH4 : (valid_sm2_private_key D )) (PreH5 : (retval_5 = 0)) (PreH6 : (0 <= retval_5)) (PreH7 : (retval_5 <= 1)) (PreH8 : (retval_5 = 0)) (PreH9 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH10 : (retval_4 = 0)) (PreH11 : (0 <= retval_4)) (PreH12 : (retval_4 <= 1)) (PreH13 : (retval_4 = 0)) (PreH14 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH15 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH16 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH17 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH18 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH19 : (K < SM2_N_Z)) (PreH20 : (0 <= K)) (PreH21 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH22 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH23 : (retval_3 = 1)) (PreH24 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH25 : (0 <= retval_2)) (PreH26 : (retval_2 <= 1)) (PreH27 : (retval_2 = 0)) (PreH28 : (K <> 0)) (PreH29 : (K < SM2_N_Z)) (PreH30 : (0 <= K)) (PreH31 : (0 <= retval)) (PreH32 : (retval <= 1)) (PreH33 : (retval = 1)) (PreH34 : (S = 0)) (PreH35 : (0 <= R)) (PreH36 : (R < SM2_N_Z)) (PreH37 : (0 <= S)) (PreH38 : (S < SM2_N_Z)) (PreH39 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH40 : (retval <> 0)) (PreH41 : (retval_2 = 0)) ,
  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "k_subtract_rda" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 ( &( "k" ) ) K )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
|--
  “ (( &( "k_subtract_rda" ) ) = ( &( "k_subtract_rda" ) )) ” 
  &&  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_N_Z) ” 
  &&  “ ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1) ” 
  &&  “ (valid_sm2_private_key D ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "k" ) ) K )
  **  (store_fn ( &( "k_subtract_rda" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
.

Definition sm2_sign_dgst_partial_solve_wit_21 := sm2_sign_dgst_partial_solve_wit_21_pure -> sm2_sign_dgst_partial_solve_wit_21_aux.

Definition sm2_sign_dgst_partial_solve_wit_22 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (K: Z) (retval_2: Z) (RX: Z) (RY: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (Ainv: Z) (PreH1 : (( &( "k_subtract_rda" ) ) = ( &( "k_subtract_rda" ) ))) (PreH2 : (0 <= Ainv)) (PreH3 : (Ainv < SM2_N_Z)) (PreH4 : ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1)) (PreH5 : (valid_sm2_private_key D )) (PreH6 : (retval_5 = 0)) (PreH7 : (0 <= retval_5)) (PreH8 : (retval_5 <= 1)) (PreH9 : (retval_5 = 0)) (PreH10 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0)) (PreH11 : (retval_4 = 0)) (PreH12 : (0 <= retval_4)) (PreH13 : (retval_4 <= 1)) (PreH14 : (retval_4 = 0)) (PreH15 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0)) (PreH16 : ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z)) (PreH17 : (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)))) (PreH18 : ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z)) (PreH19 : (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)))) (PreH20 : (K < SM2_N_Z)) (PreH21 : (0 <= K)) (PreH22 : ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z)) (PreH23 : (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)))) (PreH24 : (retval_3 = 1)) (PreH25 : (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) )) (PreH26 : (0 <= retval_2)) (PreH27 : (retval_2 <= 1)) (PreH28 : (retval_2 = 0)) (PreH29 : (K <> 0)) (PreH30 : (K < SM2_N_Z)) (PreH31 : (0 <= K)) (PreH32 : (0 <= retval)) (PreH33 : (retval <= 1)) (PreH34 : (retval = 1)) (PreH35 : (S = 0)) (PreH36 : (0 <= R)) (PreH37 : (R < SM2_N_Z)) (PreH38 : (0 <= S)) (PreH39 : (S < SM2_N_Z)) (PreH40 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH41 : (retval <> 0)) (PreH42 : (retval_2 = 0)) ,
  (store_fn ( &( "k" ) ) K )
  **  (store_fn ( &( "k_subtract_rda" ) ) (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_sm2_nh )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_u256 ( &( "s" ) ) S )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Ainv) ” 
  &&  “ (Ainv < SM2_N_Z) ” 
  &&  “ ((Zmod (((Zmod ((D + (u256_of_limbs (1) (0) (0) (0)) )) (SM2_N_Z)) * Ainv )) (SM2_N_Z)) = 1) ” 
  &&  “ (valid_sm2_private_key D ) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ (0 <= retval_5) ” 
  &&  “ (retval_5 <= 1) ” 
  &&  “ (retval_5 = 0) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) <> 0) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) <> 0) ” 
  &&  “ ((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z))) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ ((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (afpoint_represents RX RY (sm2_point_mul (K) (SM2_G_POINT)) ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (K <> 0) ” 
  &&  “ (K < SM2_N_Z) ” 
  &&  “ (0 <= K) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (S = 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "inversion_da_and_1" ) ) Ainv )
  **  (store_fn ( &( "k_subtract_rda" ) ) (Zmod ((K - (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) * D )) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "s" ) )->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn ( &( "k" ) ) K )
  **  (store_fn ( &( "r" ) ) (Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) )
  **  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_u256 ( &( "tmp" ) ) (Zmod (((Zmod (((Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) + (Zmod (RX) (SM2_N_Z)) )) (SM2_N_Z)) + K )) (SM2_N_Z)) )
  **  (store_u256 ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (store_u256 &(( &( "rand_AFPoint" ) )->ₛ "x") RX )
  **  (store_mont_jpoint ( &( "rand_JPoint" ) ) (sm2_point_mul (K) (SM2_G_POINT)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_sm2_mont_base_point_table )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (undef_sm2_signature sig_pre )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
.

Definition sm2_sign_dgst_partial_solve_wit_23 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (xs: (@list Z)) (xs_2: (@list Z)) (PreH1 : ((u64_list_value (xs_2)) = R)) (PreH2 : (u64_list_bounded xs_2 )) (PreH3 : ((Zlength (xs_2)) = 4)) (PreH4 : ((u64_list_value (xs)) = S)) (PreH5 : (u64_list_bounded xs )) (PreH6 : ((Zlength (xs)) = 4)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (S <> 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval = 0)) ,
  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "r") )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "s") )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((u64_list_value (xs_2)) = R) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ ((u64_list_value (xs)) = S) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (S <> 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval = 0) ”
  &&  (UInt64Array.undef_full &((sig_pre)  # "SM2SIG" ->ₛ "r" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "s") )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition sm2_sign_dgst_partial_solve_wit_24 := 
forall (privkey_pre: Z) (dgst_pre: Z) (sig_pre: Z) (D: Z) (DigestBytes: (@list Z)) (S: Z) (R: Z) (retval: Z) (xs: (@list Z)) (xs_2: (@list Z)) (PreH1 : ((u64_list_value (xs_2)) = R)) (PreH2 : (u64_list_bounded xs_2 )) (PreH3 : ((Zlength (xs_2)) = 4)) (PreH4 : ((u64_list_value (xs)) = S)) (PreH5 : (u64_list_bounded xs )) (PreH6 : ((Zlength (xs)) = 4)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (S <> 0)) (PreH11 : (0 <= R)) (PreH12 : (R < SM2_N_Z)) (PreH13 : (0 <= S)) (PreH14 : (S < SM2_N_Z)) (PreH15 : ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S ))) (PreH16 : (retval = 0)) ,
  (UndefStructPredu32 &((sig_pre)  # "SM2SIG" ->ₛ "s") )
  **  (UInt64Array.full &((sig_pre)  # "SM2SIG" ->ₛ "r" .ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 xs )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((u64_list_value (xs_2)) = R) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ ((u64_list_value (xs)) = S) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (S <> 0) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ (0 <= S) ” 
  &&  “ (S < SM2_N_Z) ” 
  &&  “ ((S <> 0) -> (sm2_signature_generated (be_u8_list_value (DigestBytes)) D R S )) ” 
  &&  “ (retval = 0) ”
  &&  (UInt64Array.undef_full &((sig_pre)  # "SM2SIG" ->ₛ "s" .ₛ "v") 4 )
  **  (UInt64Array.full &(( &( "s" ) )->ₛ "v") 4 xs )
  **  (UInt64Array.full &((sig_pre)  # "SM2SIG" ->ₛ "r" .ₛ "v") 4 xs_2 )
  **  (UInt64Array.full &(( &( "r" ) )->ₛ "v") 4 xs_2 )
  **  (store_bytes dgst_pre 32 DigestBytes )
  **  (store_sm2_private_key privkey_pre D )
  **  (store_fn ( &( "e" ) ) (Zmod ((be_u8_list_value (DigestBytes))) (SM2_N_Z)) )
  **  (UInt64Array.undef_full &(( &( "k" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "inversion_da_and_1" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "k_subtract_rda" ) )->ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_JPoint" ) )->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "rand_AFPoint" ) )->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_nh )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_mont_base_point_table )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_point_overwrite_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_sign_dgst_safety_wit_1 : sm2_sign_dgst_safety_wit_1.
Axiom proof_of_sm2_sign_dgst_safety_wit_2 : sm2_sign_dgst_safety_wit_2.
Axiom proof_of_sm2_sign_dgst_safety_wit_3 : sm2_sign_dgst_safety_wit_3.
Axiom proof_of_sm2_sign_dgst_safety_wit_4 : sm2_sign_dgst_safety_wit_4.
Axiom proof_of_sm2_sign_dgst_safety_wit_5 : sm2_sign_dgst_safety_wit_5.
Axiom proof_of_sm2_sign_dgst_safety_wit_6 : sm2_sign_dgst_safety_wit_6.
Axiom proof_of_sm2_sign_dgst_safety_wit_7 : sm2_sign_dgst_safety_wit_7.
Axiom proof_of_sm2_sign_dgst_safety_wit_8 : sm2_sign_dgst_safety_wit_8.
Axiom proof_of_sm2_sign_dgst_safety_wit_9 : sm2_sign_dgst_safety_wit_9.
Axiom proof_of_sm2_sign_dgst_safety_wit_10 : sm2_sign_dgst_safety_wit_10.
Axiom proof_of_sm2_sign_dgst_safety_wit_11 : sm2_sign_dgst_safety_wit_11.
Axiom proof_of_sm2_sign_dgst_safety_wit_12 : sm2_sign_dgst_safety_wit_12.
Axiom proof_of_sm2_sign_dgst_safety_wit_13 : sm2_sign_dgst_safety_wit_13.
Axiom proof_of_sm2_sign_dgst_safety_wit_14 : sm2_sign_dgst_safety_wit_14.
Axiom proof_of_sm2_sign_dgst_safety_wit_15 : sm2_sign_dgst_safety_wit_15.
Axiom proof_of_sm2_sign_dgst_safety_wit_16 : sm2_sign_dgst_safety_wit_16.
Axiom proof_of_sm2_sign_dgst_safety_wit_17 : sm2_sign_dgst_safety_wit_17.
Axiom proof_of_sm2_sign_dgst_safety_wit_18 : sm2_sign_dgst_safety_wit_18.
Axiom proof_of_sm2_sign_dgst_safety_wit_19 : sm2_sign_dgst_safety_wit_19.
Axiom proof_of_sm2_sign_dgst_safety_wit_20 : sm2_sign_dgst_safety_wit_20.
Axiom proof_of_sm2_sign_dgst_safety_wit_21 : sm2_sign_dgst_safety_wit_21.
Axiom proof_of_sm2_sign_dgst_safety_wit_22 : sm2_sign_dgst_safety_wit_22.
Axiom proof_of_sm2_sign_dgst_safety_wit_23 : sm2_sign_dgst_safety_wit_23.
Axiom proof_of_sm2_sign_dgst_safety_wit_24 : sm2_sign_dgst_safety_wit_24.
Axiom proof_of_sm2_sign_dgst_safety_wit_25 : sm2_sign_dgst_safety_wit_25.
Axiom proof_of_sm2_sign_dgst_safety_wit_26 : sm2_sign_dgst_safety_wit_26.
Axiom proof_of_sm2_sign_dgst_safety_wit_27 : sm2_sign_dgst_safety_wit_27.
Axiom proof_of_sm2_sign_dgst_safety_wit_28 : sm2_sign_dgst_safety_wit_28.
Axiom proof_of_sm2_sign_dgst_entail_wit_1 : sm2_sign_dgst_entail_wit_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_2 : sm2_sign_dgst_entail_wit_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_3_1 : sm2_sign_dgst_entail_wit_3_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_3_2 : sm2_sign_dgst_entail_wit_3_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_4_1 : sm2_sign_dgst_entail_wit_4_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_4_2 : sm2_sign_dgst_entail_wit_4_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_5_1 : sm2_sign_dgst_entail_wit_5_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_5_2 : sm2_sign_dgst_entail_wit_5_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_6_1 : sm2_sign_dgst_entail_wit_6_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_6_2 : sm2_sign_dgst_entail_wit_6_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_7 : sm2_sign_dgst_entail_wit_7.
Axiom proof_of_sm2_sign_dgst_entail_wit_8 : sm2_sign_dgst_entail_wit_8.
Axiom proof_of_sm2_sign_dgst_entail_wit_9_1 : sm2_sign_dgst_entail_wit_9_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_9_2 : sm2_sign_dgst_entail_wit_9_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_10_1 : sm2_sign_dgst_entail_wit_10_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_10_2 : sm2_sign_dgst_entail_wit_10_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_10_3 : sm2_sign_dgst_entail_wit_10_3.
Axiom proof_of_sm2_sign_dgst_entail_wit_10_4 : sm2_sign_dgst_entail_wit_10_4.
Axiom proof_of_sm2_sign_dgst_entail_wit_11_1 : sm2_sign_dgst_entail_wit_11_1.
Axiom proof_of_sm2_sign_dgst_entail_wit_11_2 : sm2_sign_dgst_entail_wit_11_2.
Axiom proof_of_sm2_sign_dgst_entail_wit_11_3 : sm2_sign_dgst_entail_wit_11_3.
Axiom proof_of_sm2_sign_dgst_entail_wit_11_4 : sm2_sign_dgst_entail_wit_11_4.
Axiom proof_of_sm2_sign_dgst_entail_wit_12 : sm2_sign_dgst_entail_wit_12.
Axiom proof_of_sm2_sign_dgst_entail_wit_13 : sm2_sign_dgst_entail_wit_13.
Axiom proof_of_sm2_sign_dgst_return_wit_1 : sm2_sign_dgst_return_wit_1.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_1 : sm2_sign_dgst_partial_solve_wit_1.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_2_pure : sm2_sign_dgst_partial_solve_wit_2_pure.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_2 : sm2_sign_dgst_partial_solve_wit_2.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_3 : sm2_sign_dgst_partial_solve_wit_3.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_4 : sm2_sign_dgst_partial_solve_wit_4.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_5 : sm2_sign_dgst_partial_solve_wit_5.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_6 : sm2_sign_dgst_partial_solve_wit_6.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_7_pure : sm2_sign_dgst_partial_solve_wit_7_pure.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_7 : sm2_sign_dgst_partial_solve_wit_7.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_8_pure : sm2_sign_dgst_partial_solve_wit_8_pure.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_8 : sm2_sign_dgst_partial_solve_wit_8.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_9 : sm2_sign_dgst_partial_solve_wit_9.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_10 : sm2_sign_dgst_partial_solve_wit_10.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_11 : sm2_sign_dgst_partial_solve_wit_11.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_12 : sm2_sign_dgst_partial_solve_wit_12.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_13 : sm2_sign_dgst_partial_solve_wit_13.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_14 : sm2_sign_dgst_partial_solve_wit_14.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_15 : sm2_sign_dgst_partial_solve_wit_15.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_16 : sm2_sign_dgst_partial_solve_wit_16.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_17 : sm2_sign_dgst_partial_solve_wit_17.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_18_pure : sm2_sign_dgst_partial_solve_wit_18_pure.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_18 : sm2_sign_dgst_partial_solve_wit_18.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_19_pure : sm2_sign_dgst_partial_solve_wit_19_pure.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_19 : sm2_sign_dgst_partial_solve_wit_19.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_20 : sm2_sign_dgst_partial_solve_wit_20.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_21_pure : sm2_sign_dgst_partial_solve_wit_21_pure.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_21 : sm2_sign_dgst_partial_solve_wit_21.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_22 : sm2_sign_dgst_partial_solve_wit_22.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_23 : sm2_sign_dgst_partial_solve_wit_23.
Axiom proof_of_sm2_sign_dgst_partial_solve_wit_24 : sm2_sign_dgst_partial_solve_wit_24.

End VC_Correct.
