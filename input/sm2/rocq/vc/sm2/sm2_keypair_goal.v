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
From SimpleC.EE.Applications_human.sm2.vc.sm2 Require Import sm2_keypair_def.
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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_protocol_views_strategy_proof.

(*----- Function sm2_keypair -----*)

Definition sm2_keypair_safety_wit_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) ,
  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
  **  (store_sm2_keypair_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_keypair_safety_wit_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) ,
  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
  **  (store_sm2_keypair_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_keypair_safety_wit_3 := 
forall (privkey_pre: Z) (pubkey_pre: Z) ,
  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
  **  (store_sm2_keypair_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_keypair_safety_wit_4 := 
forall (privkey_pre: Z) (pubkey_pre: Z) ,
  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
  **  (store_sm2_keypair_globals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm2_keypair_safety_wit_5 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (DPlus = 0)) (PreH5 : (retval = 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (D = 0)) (PreH10 : (0 <= D)) (PreH11 : (D < SM2_N_Z)) (PreH12 : (0 <= DPlus)) (PreH13 : (DPlus < SM2_N_Z)) (PreH14 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ False ”
.

Definition sm2_keypair_safety_wit_6 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (DPlus <> 0)) (PreH5 : (retval = 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 1)) (PreH9 : (D = 0)) (PreH10 : (0 <= D)) (PreH11 : (D < SM2_N_Z)) (PreH12 : (0 <= DPlus)) (PreH13 : (DPlus < SM2_N_Z)) (PreH14 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ False ”
.

Definition sm2_keypair_safety_wit_7 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (DPlus = 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ False ”
.

Definition sm2_keypair_safety_wit_8 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (D <> 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ False ”
.

Definition sm2_keypair_safety_wit_9 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ False ”
.

Definition sm2_keypair_entail_wit_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) ,
  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
  **  (store_sm2_keypair_globals )
|--
  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
.

Definition sm2_keypair_entail_wit_2_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus_2: Z) (D_2: Z) (retval: Z) (K: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (D_2 = 0)) (PreH6 : (0 <= D_2)) (PreH7 : (D_2 < SM2_N_Z)) (PreH8 : (0 <= DPlus_2)) (PreH9 : (DPlus_2 < SM2_N_Z)) (PreH10 : (DPlus_2 = (Zmod ((D_2 + 1 )) (SM2_N_Z)))) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_fn ( &( "d_plus_one" ) ) (Zmod ((K + 1 )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
|--
  EX (DPlus: Z)  (D: Z) ,
  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_entail_wit_2_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus_2: Z) (D_2: Z) (retval: Z) (retval_2: Z) (K: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (DPlus_2 = 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D_2 <> 0)) (PreH11 : (0 <= D_2)) (PreH12 : (D_2 < SM2_N_Z)) (PreH13 : (0 <= DPlus_2)) (PreH14 : (DPlus_2 < SM2_N_Z)) (PreH15 : (DPlus_2 = (Zmod ((D_2 + 1 )) (SM2_N_Z)))) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_fn ( &( "d_plus_one" ) ) (Zmod ((K + 1 )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
|--
  EX (DPlus: Z)  (D: Z) ,
  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_entail_wit_3 := 
(
forall (privkey_pre: Z) (pubkey_pre: Z) (K: Z) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_fn ( &( "one" ) ) (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )
  **  (store_fn ( &( "d_plus_one" ) ) (Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  EX (DPlus: Z)  (D: Z) ,
  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
) \/
(
forall (K: Z) (PreH1 : ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)))) (PreH3 : (K < SM2_N_Z)) (PreH4 : (0 <= K)) ,
  TT && emp 
|--
  “ ((Zmod ((K + 1 )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ (0 <= (Zmod ((K + 1 )) (SM2_N_Z))) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1) ” 
  &&  “ ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) = (Zmod ((K + 1 )) (SM2_N_Z))) ”
  &&  emp
).

Definition sm2_keypair_entail_wit_3_split_goal_1 := 
forall (K: Z) (PreH1 : ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)))) (PreH3 : (K < SM2_N_Z)) (PreH4 : (0 <= K)) ,
  ((Zmod ((K + 1 )) (SM2_N_Z)) < SM2_N_Z)
.

Definition sm2_keypair_entail_wit_3_split_goal_2 := 
forall (K: Z) (PreH1 : ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)))) (PreH3 : (K < SM2_N_Z)) (PreH4 : (0 <= K)) ,
  (0 <= (Zmod ((K + 1 )) (SM2_N_Z)))
.

Definition sm2_keypair_entail_wit_3_split_goal_3 := 
forall (K: Z) (PreH1 : ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)))) (PreH3 : (K < SM2_N_Z)) (PreH4 : (0 <= K)) ,
  ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) = 1)
.

Definition sm2_keypair_entail_wit_3_split_goal_4 := 
forall (K: Z) (PreH1 : ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) < SM2_N_Z)) (PreH2 : (0 <= (Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)))) (PreH3 : (K < SM2_N_Z)) (PreH4 : (0 <= K)) ,
  ((Zmod ((K + (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )) (SM2_N_Z)) = (Zmod ((K + 1 )) (SM2_N_Z)))
.

Definition sm2_keypair_entail_wit_4_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (DPlus <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_entail_wit_4_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (DPlus = 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (DPlus <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_entail_wit_5_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (D <> 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  (EX (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (D = 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals ))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 <> 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (DPlus = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals ))
.

Definition sm2_keypair_entail_wit_5_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (D = 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (D = 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_entail_wit_5_3 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval_2: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (0 <= retval_4)) (PreH3 : (retval_4 <= 1)) (PreH4 : (retval_4 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  (EX (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (D = 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals ))
  ||
  (EX (retval_3: Z) ,
  “ (retval_3 <> 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (DPlus = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals ))
.

Definition sm2_keypair_entail_wit_5_4 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (DPlus = 0)) (PreH6 : (retval_2 = 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (DPlus = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_return_wit_1 := 
(
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D_2 <> 0)) (PreH11 : (0 <= D_2)) (PreH12 : (D_2 < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D_2 + 1 )) (SM2_N_Z)))) ,
  (store_sm2_private_key privkey_pre D_2 )
  **  (store_sm2_public_key pubkey_pre (sm2_point_mul (D_2) (SM2_G_POINT)) )
  **  (store_sm2_get_public_key_globals )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
|--
  EX (D: Z) ,
  (store_sm2_private_key privkey_pre D )
  **  (store_sm2_public_key pubkey_pre (sm2_point_mul (D) (SM2_G_POINT)) )
  **  (store_sm2_keypair_globals )
) \/
(
forall (DPlus: Z) (D_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D_2 <> 0)) (PreH11 : (0 <= D_2)) (PreH12 : (D_2 < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D_2 + 1 )) (SM2_N_Z)))) ,
  (store_sm2_get_public_key_globals )
|--
  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
).

Definition sm2_keypair_return_wit_1_split_goal_spatial := 
forall (DPlus: Z) (D_2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D_2 <> 0)) (PreH11 : (0 <= D_2)) (PreH12 : (D_2 < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D_2 + 1 )) (SM2_N_Z)))) ,
  (store_sm2_get_public_key_globals )
|--
  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
.

Definition sm2_keypair_partial_solve_wit_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) ,
  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (store_sm2_rhon )
  **  (store_sm2_n )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (undef_sm2_private_key privkey_pre )
|--
  (UInt64Array.undef_full &((privkey_pre)  # "PrivKey" ->ₛ "da" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (UndefStructPredAFPoint pubkey_pre )
.

Definition sm2_keypair_partial_solve_wit_2_pure := 
(
forall (privkey_pre: Z) (pubkey_pre: Z) (K: Z) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ (0 <= (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) )))) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) < SM2_N_Z) ”
) \/
(
forall (privkey_pre: Z) (pubkey_pre: Z) (K: Z) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) < SM2_N_Z) ” 
  &&  “ (0 <= (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) )))) ”
).

Definition sm2_keypair_partial_solve_wit_2_pure_split_goal_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (K: Z) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) < SM2_N_Z) ”
.

Definition sm2_keypair_partial_solve_wit_2_pure_split_goal_2 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (K: Z) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ (0 <= (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) )))) ”
.

Definition sm2_keypair_partial_solve_wit_2_aux := 
forall (privkey_pre: Z) (pubkey_pre: Z) (K: Z) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredu32 ( &( "d_plus_one" ) ) )
  **  (UInt64Array.full &(( &( "one" ) )->ₛ "v") 4 ((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ) )
  **  (UndefStructPredAFPoint pubkey_pre )
|--
  “ (0 <= (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) )))) ” 
  &&  “ ((u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) < SM2_N_Z) ”
  &&  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_fn ( &( "one" ) ) (u64_list_value (((make_record_u32 ((cons (1) ((repeat_Z (0) (3)))))).(u32_v) ))) )
  **  (UInt64Array.undef_full &(( &( "d_plus_one" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_inv2p )
  **  (store_jpoint_zero )
  **  (store_sm2_rhop )
  **  (store_sm2_p )
  **  (store_sm2_base_point_table )
  **  (UndefStructPredAFPoint pubkey_pre )
.

Definition sm2_keypair_partial_solve_wit_2 := sm2_keypair_partial_solve_wit_2_pure -> sm2_keypair_partial_solve_wit_2_aux.

Definition sm2_keypair_partial_solve_wit_3 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (K: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (D = 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (D = 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UInt64Array.undef_full &(( &( "d_plus_one" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_4 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (K: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (DPlus = 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (DPlus = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_fn &((privkey_pre)  # "PrivKey" ->ₛ "da") K )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UInt64Array.undef_full &(( &( "d_plus_one" ) )->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_5 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (D = 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (D = 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (UInt64Array.undef_full &((privkey_pre)  # "PrivKey" ->ₛ "da" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_6 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (DPlus = 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (DPlus = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (UInt64Array.undef_full &((privkey_pre)  # "PrivKey" ->ₛ "da" .ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_7 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (PreH1 : (0 <= D)) (PreH2 : (D < SM2_N_Z)) (PreH3 : (0 <= DPlus)) (PreH4 : (DPlus < SM2_N_Z)) (PreH5 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_8 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (D <> 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_9 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (D = 0)) (PreH6 : (0 <= D)) (PreH7 : (D < SM2_N_Z)) (PreH8 : (0 <= DPlus)) (PreH9 : (DPlus < SM2_N_Z)) (PreH10 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (D = 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
.

Definition sm2_keypair_partial_solve_wit_10_pure := 
(
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (valid_sm2_private_key D ) ”
) \/
(
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (valid_sm2_private_key D ) ”
).

Definition sm2_keypair_partial_solve_wit_10_pure_split_goal_1 := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  ((( &( "privkey" ) )) # Ptr  |-> privkey_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (valid_sm2_private_key D ) ”
.

Definition sm2_keypair_partial_solve_wit_10_aux := 
forall (privkey_pre: Z) (pubkey_pre: Z) (DPlus: Z) (D: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (DPlus <> 0)) (PreH6 : (retval = 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (D <> 0)) (PreH11 : (0 <= D)) (PreH12 : (D < SM2_N_Z)) (PreH13 : (0 <= DPlus)) (PreH14 : (DPlus < SM2_N_Z)) (PreH15 : (DPlus = (Zmod ((D + 1 )) (SM2_N_Z)))) ,
  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_u256 &((privkey_pre)  # "PrivKey" ->ₛ "da") D )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_get_public_key_globals )
|--
  “ (valid_sm2_private_key D ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (DPlus <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (D <> 0) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D < SM2_N_Z) ” 
  &&  “ (0 <= DPlus) ” 
  &&  “ (DPlus < SM2_N_Z) ” 
  &&  “ (DPlus = (Zmod ((D + 1 )) (SM2_N_Z))) ”
  &&  (store_sm2_private_key privkey_pre D )
  **  (UndefStructPredAFPoint pubkey_pre )
  **  (store_sm2_get_public_key_globals )
  **  (store_u256 ( &( "d_plus_one" ) ) DPlus )
  **  (store_fn ( &( "one" ) ) 1 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
.

Definition sm2_keypair_partial_solve_wit_10 := sm2_keypair_partial_solve_wit_10_pure -> sm2_keypair_partial_solve_wit_10_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.

Axiom proof_of_sm2_keypair_safety_wit_1 : sm2_keypair_safety_wit_1.
Axiom proof_of_sm2_keypair_safety_wit_2 : sm2_keypair_safety_wit_2.
Axiom proof_of_sm2_keypair_safety_wit_3 : sm2_keypair_safety_wit_3.
Axiom proof_of_sm2_keypair_safety_wit_4 : sm2_keypair_safety_wit_4.
Axiom proof_of_sm2_keypair_safety_wit_5 : sm2_keypair_safety_wit_5.
Axiom proof_of_sm2_keypair_safety_wit_6 : sm2_keypair_safety_wit_6.
Axiom proof_of_sm2_keypair_safety_wit_7 : sm2_keypair_safety_wit_7.
Axiom proof_of_sm2_keypair_safety_wit_8 : sm2_keypair_safety_wit_8.
Axiom proof_of_sm2_keypair_safety_wit_9 : sm2_keypair_safety_wit_9.
Axiom proof_of_sm2_keypair_entail_wit_1 : sm2_keypair_entail_wit_1.
Axiom proof_of_sm2_keypair_entail_wit_2_1 : sm2_keypair_entail_wit_2_1.
Axiom proof_of_sm2_keypair_entail_wit_2_2 : sm2_keypair_entail_wit_2_2.
Axiom proof_of_sm2_keypair_entail_wit_3 : sm2_keypair_entail_wit_3.
Axiom proof_of_sm2_keypair_entail_wit_4_1 : sm2_keypair_entail_wit_4_1.
Axiom proof_of_sm2_keypair_entail_wit_4_2 : sm2_keypair_entail_wit_4_2.
Axiom proof_of_sm2_keypair_entail_wit_5_1 : sm2_keypair_entail_wit_5_1.
Axiom proof_of_sm2_keypair_entail_wit_5_2 : sm2_keypair_entail_wit_5_2.
Axiom proof_of_sm2_keypair_entail_wit_5_3 : sm2_keypair_entail_wit_5_3.
Axiom proof_of_sm2_keypair_entail_wit_5_4 : sm2_keypair_entail_wit_5_4.
Axiom proof_of_sm2_keypair_return_wit_1 : sm2_keypair_return_wit_1.
Axiom proof_of_sm2_keypair_partial_solve_wit_1 : sm2_keypair_partial_solve_wit_1.
Axiom proof_of_sm2_keypair_partial_solve_wit_2_pure : sm2_keypair_partial_solve_wit_2_pure.
Axiom proof_of_sm2_keypair_partial_solve_wit_2 : sm2_keypair_partial_solve_wit_2.
Axiom proof_of_sm2_keypair_partial_solve_wit_3 : sm2_keypair_partial_solve_wit_3.
Axiom proof_of_sm2_keypair_partial_solve_wit_4 : sm2_keypair_partial_solve_wit_4.
Axiom proof_of_sm2_keypair_partial_solve_wit_5 : sm2_keypair_partial_solve_wit_5.
Axiom proof_of_sm2_keypair_partial_solve_wit_6 : sm2_keypair_partial_solve_wit_6.
Axiom proof_of_sm2_keypair_partial_solve_wit_7 : sm2_keypair_partial_solve_wit_7.
Axiom proof_of_sm2_keypair_partial_solve_wit_8 : sm2_keypair_partial_solve_wit_8.
Axiom proof_of_sm2_keypair_partial_solve_wit_9 : sm2_keypair_partial_solve_wit_9.
Axiom proof_of_sm2_keypair_partial_solve_wit_10_pure : sm2_keypair_partial_solve_wit_10_pure.
Axiom proof_of_sm2_keypair_partial_solve_wit_10 : sm2_keypair_partial_solve_wit_10.

End VC_Correct.
