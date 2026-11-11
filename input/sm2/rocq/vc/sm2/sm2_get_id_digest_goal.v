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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_za_buffers_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_za_buffers_strategy_proof.

(*----- Function sm2_get_id_digest -----*)

Definition sm2_get_id_digest_safety_wit_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (50 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 50) ”
.

Definition sm2_get_id_digest_safety_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (id_len_pre > 50)) (PreH2 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sm2_get_id_digest_safety_wit_3 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (id_len_pre > 50)) (PreH2 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm2_get_id_digest_safety_wit_4 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (id_len_pre <= 50)) (PreH2 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_5 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_6 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (256 <> 0) ”
.

Definition sm2_get_id_digest_safety_wit_7 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (8 <= 63) ” 
  &&  “ (0 <= 8) ”
.

Definition sm2_get_id_digest_safety_wit_8 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm2_get_id_digest_safety_wit_9 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm2_get_id_digest_safety_wit_10 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition sm2_get_id_digest_safety_wit_11 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sm2_get_id_digest_safety_wit_12 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (256 <> 0) ”
.

Definition sm2_get_id_digest_safety_wit_13 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sm2_get_id_digest_safety_wit_14 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition sm2_get_id_digest_safety_wit_15 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : ((2 + id_len_pre ) <= 250)) (PreH2 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH3 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH4 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH5 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH6 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH7 : ((u8_list_value (bytes_4)) = y)) (PreH8 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH9 : ((u8_list_value (bytes_3)) = x)) (PreH10 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH11 : ((u8_list_value (bytes_2)) = y_2)) (PreH12 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH13 : ((u8_list_value (bytes)) = x_2)) (PreH14 : (x_2 < SM2_P_Z)) (PreH15 : (0 <= x_2)) (PreH16 : (y_2 < SM2_P_Z)) (PreH17 : (0 <= y_2)) (PreH18 : (x < SM2_P_Z)) (PreH19 : (0 <= x)) (PreH20 : (y < SM2_P_Z)) (PreH21 : (0 <= y)) (PreH22 : (SM2_A_Z < SM2_P_Z)) (PreH23 : (0 <= SM2_A_Z)) (PreH24 : (SM2_B_Z < SM2_P_Z)) (PreH25 : (0 <= SM2_B_Z)) (PreH26 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH27 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH28 : (y_2 = (sm2_point_y (P)))) (PreH29 : (x_2 = (sm2_point_x (P)))) (PreH30 : (afpoint_represents x_2 y_2 P )) (PreH31 : (afpoint_represents x y SM2_G_POINT )) (PreH32 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH33 : (id_len_pre <= 50)) (PreH34 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_16 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : ((2 + id_len_pre ) <= 250)) (PreH2 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH3 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH4 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH5 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH6 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH7 : ((u8_list_value (bytes_4)) = y)) (PreH8 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH9 : ((u8_list_value (bytes_3)) = x)) (PreH10 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH11 : ((u8_list_value (bytes_2)) = y_2)) (PreH12 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH13 : ((u8_list_value (bytes)) = x_2)) (PreH14 : (x_2 < SM2_P_Z)) (PreH15 : (0 <= x_2)) (PreH16 : (y_2 < SM2_P_Z)) (PreH17 : (0 <= y_2)) (PreH18 : (x < SM2_P_Z)) (PreH19 : (0 <= x)) (PreH20 : (y < SM2_P_Z)) (PreH21 : (0 <= y)) (PreH22 : (SM2_A_Z < SM2_P_Z)) (PreH23 : (0 <= SM2_A_Z)) (PreH24 : (SM2_B_Z < SM2_P_Z)) (PreH25 : (0 <= SM2_B_Z)) (PreH26 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH27 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH28 : (y_2 = (sm2_point_y (P)))) (PreH29 : (x_2 = (sm2_point_x (P)))) (PreH30 : (afpoint_represents x_2 y_2 P )) (PreH31 : (afpoint_represents x y SM2_G_POINT )) (PreH32 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH33 : (id_len_pre <= 50)) (PreH34 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sm2_get_id_digest_safety_wit_17 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH2 : ((Zlength (ID)) = id_len_pre)) (PreH3 : (u8_list_bounded ID )) (PreH4 : ((2 + id_len_pre ) <= 250)) (PreH5 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH6 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH7 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH8 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH9 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_4)) = y)) (PreH11 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH12 : ((u8_list_value (bytes_3)) = x)) (PreH13 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH14 : ((u8_list_value (bytes_2)) = y_2)) (PreH15 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH16 : ((u8_list_value (bytes)) = x_2)) (PreH17 : (x_2 < SM2_P_Z)) (PreH18 : (0 <= x_2)) (PreH19 : (y_2 < SM2_P_Z)) (PreH20 : (0 <= y_2)) (PreH21 : (x < SM2_P_Z)) (PreH22 : (0 <= x)) (PreH23 : (y < SM2_P_Z)) (PreH24 : (0 <= y)) (PreH25 : (SM2_A_Z < SM2_P_Z)) (PreH26 : (0 <= SM2_A_Z)) (PreH27 : (SM2_B_Z < SM2_P_Z)) (PreH28 : (0 <= SM2_B_Z)) (PreH29 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH30 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH31 : (y_2 = (sm2_point_y (P)))) (PreH32 : (x_2 = (sm2_point_x (P)))) (PreH33 : (afpoint_represents x_2 y_2 P )) (PreH34 : (afpoint_represents x y SM2_G_POINT )) (PreH35 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH36 : (id_len_pre <= 50)) (PreH37 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_18 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH2 : ((Zlength (ID)) = id_len_pre)) (PreH3 : (u8_list_bounded ID )) (PreH4 : ((2 + id_len_pre ) <= 250)) (PreH5 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH6 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH7 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH8 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH9 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_4)) = y)) (PreH11 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH12 : ((u8_list_value (bytes_3)) = x)) (PreH13 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH14 : ((u8_list_value (bytes_2)) = y_2)) (PreH15 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH16 : ((u8_list_value (bytes)) = x_2)) (PreH17 : (x_2 < SM2_P_Z)) (PreH18 : (0 <= x_2)) (PreH19 : (y_2 < SM2_P_Z)) (PreH20 : (0 <= y_2)) (PreH21 : (x < SM2_P_Z)) (PreH22 : (0 <= x)) (PreH23 : (y < SM2_P_Z)) (PreH24 : (0 <= y)) (PreH25 : (SM2_A_Z < SM2_P_Z)) (PreH26 : (0 <= SM2_A_Z)) (PreH27 : (SM2_B_Z < SM2_P_Z)) (PreH28 : (0 <= SM2_B_Z)) (PreH29 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH30 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH31 : (y_2 = (sm2_point_y (P)))) (PreH32 : (x_2 = (sm2_point_x (P)))) (PreH33 : (afpoint_represents x_2 y_2 P )) (PreH34 : (afpoint_represents x y SM2_G_POINT )) (PreH35 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH36 : (id_len_pre <= 50)) (PreH37 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_19 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_5)) = 32)) (PreH3 : (u8_list_bounded bytes_5 )) (PreH4 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH5 : ((Zlength (ID)) = id_len_pre)) (PreH6 : (u8_list_bounded ID )) (PreH7 : ((2 + id_len_pre ) <= 250)) (PreH8 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH9 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH10 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH11 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH12 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH13 : ((u8_list_value (bytes_4)) = y)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH15 : ((u8_list_value (bytes_3)) = x)) (PreH16 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH17 : ((u8_list_value (bytes_2)) = y_2)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH19 : ((u8_list_value (bytes)) = x_2)) (PreH20 : (x_2 < SM2_P_Z)) (PreH21 : (0 <= x_2)) (PreH22 : (y_2 < SM2_P_Z)) (PreH23 : (0 <= y_2)) (PreH24 : (x < SM2_P_Z)) (PreH25 : (0 <= x)) (PreH26 : (y < SM2_P_Z)) (PreH27 : (0 <= y)) (PreH28 : (SM2_A_Z < SM2_P_Z)) (PreH29 : (0 <= SM2_A_Z)) (PreH30 : (SM2_B_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_B_Z)) (PreH32 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH33 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH34 : (y_2 = (sm2_point_y (P)))) (PreH35 : (x_2 = (sm2_point_x (P)))) (PreH36 : (afpoint_represents x_2 y_2 P )) (PreH37 : (afpoint_represents x y SM2_G_POINT )) (PreH38 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH39 : (id_len_pre <= 50)) (PreH40 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) bytes_5 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_20 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_5)) = 32)) (PreH3 : (u8_list_bounded bytes_5 )) (PreH4 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH5 : ((Zlength (ID)) = id_len_pre)) (PreH6 : (u8_list_bounded ID )) (PreH7 : ((2 + id_len_pre ) <= 250)) (PreH8 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH9 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH10 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH11 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH12 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH13 : ((u8_list_value (bytes_4)) = y)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH15 : ((u8_list_value (bytes_3)) = x)) (PreH16 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH17 : ((u8_list_value (bytes_2)) = y_2)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH19 : ((u8_list_value (bytes)) = x_2)) (PreH20 : (x_2 < SM2_P_Z)) (PreH21 : (0 <= x_2)) (PreH22 : (y_2 < SM2_P_Z)) (PreH23 : (0 <= y_2)) (PreH24 : (x < SM2_P_Z)) (PreH25 : (0 <= x)) (PreH26 : (y < SM2_P_Z)) (PreH27 : (0 <= y)) (PreH28 : (SM2_A_Z < SM2_P_Z)) (PreH29 : (0 <= SM2_A_Z)) (PreH30 : (SM2_B_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_B_Z)) (PreH32 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH33 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH34 : (y_2 = (sm2_point_y (P)))) (PreH35 : (x_2 = (sm2_point_x (P)))) (PreH36 : (afpoint_represents x_2 y_2 P )) (PreH37 : (afpoint_represents x y SM2_G_POINT )) (PreH38 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH39 : (id_len_pre <= 50)) (PreH40 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) bytes_5 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_21 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (u8_list_bounded (rev (bytes_5)) )) (PreH2 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH3 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_5)) = 32)) (PreH5 : (u8_list_bounded bytes_5 )) (PreH6 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH7 : ((Zlength (ID)) = id_len_pre)) (PreH8 : (u8_list_bounded ID )) (PreH9 : ((2 + id_len_pre ) <= 250)) (PreH10 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH11 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH12 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH13 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH15 : ((u8_list_value (bytes_4)) = y)) (PreH16 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH17 : ((u8_list_value (bytes_3)) = x)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH19 : ((u8_list_value (bytes_2)) = y_2)) (PreH20 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH21 : ((u8_list_value (bytes)) = x_2)) (PreH22 : (x_2 < SM2_P_Z)) (PreH23 : (0 <= x_2)) (PreH24 : (y_2 < SM2_P_Z)) (PreH25 : (0 <= y_2)) (PreH26 : (x < SM2_P_Z)) (PreH27 : (0 <= x)) (PreH28 : (y < SM2_P_Z)) (PreH29 : (0 <= y)) (PreH30 : (SM2_A_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_A_Z)) (PreH32 : (SM2_B_Z < SM2_P_Z)) (PreH33 : (0 <= SM2_B_Z)) (PreH34 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH35 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH36 : (y_2 = (sm2_point_y (P)))) (PreH37 : (x_2 = (sm2_point_x (P)))) (PreH38 : (afpoint_represents x_2 y_2 P )) (PreH39 : (afpoint_represents x y SM2_G_POINT )) (PreH40 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH41 : (id_len_pre <= 50)) (PreH42 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_22 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (u8_list_bounded (rev (bytes_5)) )) (PreH2 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH3 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_5)) = 32)) (PreH5 : (u8_list_bounded bytes_5 )) (PreH6 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH7 : ((Zlength (ID)) = id_len_pre)) (PreH8 : (u8_list_bounded ID )) (PreH9 : ((2 + id_len_pre ) <= 250)) (PreH10 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH11 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH12 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH13 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH15 : ((u8_list_value (bytes_4)) = y)) (PreH16 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH17 : ((u8_list_value (bytes_3)) = x)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH19 : ((u8_list_value (bytes_2)) = y_2)) (PreH20 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH21 : ((u8_list_value (bytes)) = x_2)) (PreH22 : (x_2 < SM2_P_Z)) (PreH23 : (0 <= x_2)) (PreH24 : (y_2 < SM2_P_Z)) (PreH25 : (0 <= y_2)) (PreH26 : (x < SM2_P_Z)) (PreH27 : (0 <= x)) (PreH28 : (y < SM2_P_Z)) (PreH29 : (0 <= y)) (PreH30 : (SM2_A_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_A_Z)) (PreH32 : (SM2_B_Z < SM2_P_Z)) (PreH33 : (0 <= SM2_B_Z)) (PreH34 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH35 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH36 : (y_2 = (sm2_point_y (P)))) (PreH37 : (x_2 = (sm2_point_x (P)))) (PreH38 : (afpoint_represents x_2 y_2 P )) (PreH39 : (afpoint_represents x y SM2_G_POINT )) (PreH40 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH41 : (id_len_pre <= 50)) (PreH42 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_23 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (u8_list_bounded (rev (bytes_5)) )) (PreH2 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH3 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_5)) = 32)) (PreH5 : (u8_list_bounded bytes_5 )) (PreH6 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH7 : ((Zlength (ID)) = id_len_pre)) (PreH8 : (u8_list_bounded ID )) (PreH9 : ((2 + id_len_pre ) <= 250)) (PreH10 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH11 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH12 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH13 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH15 : ((u8_list_value (bytes_4)) = y)) (PreH16 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH17 : ((u8_list_value (bytes_3)) = x)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH19 : ((u8_list_value (bytes_2)) = y_2)) (PreH20 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH21 : ((u8_list_value (bytes)) = x_2)) (PreH22 : (x_2 < SM2_P_Z)) (PreH23 : (0 <= x_2)) (PreH24 : (y_2 < SM2_P_Z)) (PreH25 : (0 <= y_2)) (PreH26 : (x < SM2_P_Z)) (PreH27 : (0 <= x)) (PreH28 : (y < SM2_P_Z)) (PreH29 : (0 <= y)) (PreH30 : (SM2_A_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_A_Z)) (PreH32 : (SM2_B_Z < SM2_P_Z)) (PreH33 : (0 <= SM2_B_Z)) (PreH34 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH35 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH36 : (y_2 = (sm2_point_y (P)))) (PreH37 : (x_2 = (sm2_point_x (P)))) (PreH38 : (afpoint_represents x_2 y_2 P )) (PreH39 : (afpoint_represents x y SM2_G_POINT )) (PreH40 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH41 : (id_len_pre <= 50)) (PreH42 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_24 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_6)) = 32)) (PreH3 : (u8_list_bounded bytes_6 )) (PreH4 : (u8_list_bounded (rev (bytes_5)) )) (PreH5 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH6 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_5)) = 32)) (PreH8 : (u8_list_bounded bytes_5 )) (PreH9 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH10 : ((Zlength (ID)) = id_len_pre)) (PreH11 : (u8_list_bounded ID )) (PreH12 : ((2 + id_len_pre ) <= 250)) (PreH13 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH14 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH15 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH16 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH17 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH18 : ((u8_list_value (bytes_4)) = y)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH20 : ((u8_list_value (bytes_3)) = x)) (PreH21 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH22 : ((u8_list_value (bytes_2)) = y_2)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH24 : ((u8_list_value (bytes)) = x_2)) (PreH25 : (x_2 < SM2_P_Z)) (PreH26 : (0 <= x_2)) (PreH27 : (y_2 < SM2_P_Z)) (PreH28 : (0 <= y_2)) (PreH29 : (x < SM2_P_Z)) (PreH30 : (0 <= x)) (PreH31 : (y < SM2_P_Z)) (PreH32 : (0 <= y)) (PreH33 : (SM2_A_Z < SM2_P_Z)) (PreH34 : (0 <= SM2_A_Z)) (PreH35 : (SM2_B_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_B_Z)) (PreH37 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH38 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH39 : (y_2 = (sm2_point_y (P)))) (PreH40 : (x_2 = (sm2_point_x (P)))) (PreH41 : (afpoint_represents x_2 y_2 P )) (PreH42 : (afpoint_represents x y SM2_G_POINT )) (PreH43 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH44 : (id_len_pre <= 50)) (PreH45 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) bytes_6 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_25 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_6)) = 32)) (PreH3 : (u8_list_bounded bytes_6 )) (PreH4 : (u8_list_bounded (rev (bytes_5)) )) (PreH5 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH6 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_5)) = 32)) (PreH8 : (u8_list_bounded bytes_5 )) (PreH9 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH10 : ((Zlength (ID)) = id_len_pre)) (PreH11 : (u8_list_bounded ID )) (PreH12 : ((2 + id_len_pre ) <= 250)) (PreH13 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH14 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH15 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH16 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH17 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH18 : ((u8_list_value (bytes_4)) = y)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH20 : ((u8_list_value (bytes_3)) = x)) (PreH21 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH22 : ((u8_list_value (bytes_2)) = y_2)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH24 : ((u8_list_value (bytes)) = x_2)) (PreH25 : (x_2 < SM2_P_Z)) (PreH26 : (0 <= x_2)) (PreH27 : (y_2 < SM2_P_Z)) (PreH28 : (0 <= y_2)) (PreH29 : (x < SM2_P_Z)) (PreH30 : (0 <= x)) (PreH31 : (y < SM2_P_Z)) (PreH32 : (0 <= y)) (PreH33 : (SM2_A_Z < SM2_P_Z)) (PreH34 : (0 <= SM2_A_Z)) (PreH35 : (SM2_B_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_B_Z)) (PreH37 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH38 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH39 : (y_2 = (sm2_point_y (P)))) (PreH40 : (x_2 = (sm2_point_x (P)))) (PreH41 : (afpoint_represents x_2 y_2 P )) (PreH42 : (afpoint_represents x y SM2_G_POINT )) (PreH43 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH44 : (id_len_pre <= 50)) (PreH45 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) bytes_6 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_26 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_6)) = 32)) (PreH3 : (u8_list_bounded bytes_6 )) (PreH4 : (u8_list_bounded (rev (bytes_5)) )) (PreH5 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH6 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_5)) = 32)) (PreH8 : (u8_list_bounded bytes_5 )) (PreH9 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH10 : ((Zlength (ID)) = id_len_pre)) (PreH11 : (u8_list_bounded ID )) (PreH12 : ((2 + id_len_pre ) <= 250)) (PreH13 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH14 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH15 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH16 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH17 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH18 : ((u8_list_value (bytes_4)) = y)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH20 : ((u8_list_value (bytes_3)) = x)) (PreH21 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH22 : ((u8_list_value (bytes_2)) = y_2)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH24 : ((u8_list_value (bytes)) = x_2)) (PreH25 : (x_2 < SM2_P_Z)) (PreH26 : (0 <= x_2)) (PreH27 : (y_2 < SM2_P_Z)) (PreH28 : (0 <= y_2)) (PreH29 : (x < SM2_P_Z)) (PreH30 : (0 <= x)) (PreH31 : (y < SM2_P_Z)) (PreH32 : (0 <= y)) (PreH33 : (SM2_A_Z < SM2_P_Z)) (PreH34 : (0 <= SM2_A_Z)) (PreH35 : (SM2_B_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_B_Z)) (PreH37 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH38 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH39 : (y_2 = (sm2_point_y (P)))) (PreH40 : (x_2 = (sm2_point_x (P)))) (PreH41 : (afpoint_represents x_2 y_2 P )) (PreH42 : (afpoint_represents x y SM2_G_POINT )) (PreH43 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH44 : (id_len_pre <= 50)) (PreH45 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) bytes_6 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_27 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (u8_list_bounded (rev (bytes_6)) )) (PreH2 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH3 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_6)) = 32)) (PreH5 : (u8_list_bounded bytes_6 )) (PreH6 : (u8_list_bounded (rev (bytes_5)) )) (PreH7 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH8 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_5)) = 32)) (PreH10 : (u8_list_bounded bytes_5 )) (PreH11 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH12 : ((Zlength (ID)) = id_len_pre)) (PreH13 : (u8_list_bounded ID )) (PreH14 : ((2 + id_len_pre ) <= 250)) (PreH15 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH16 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH17 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH18 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH20 : ((u8_list_value (bytes_4)) = y)) (PreH21 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH22 : ((u8_list_value (bytes_3)) = x)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH24 : ((u8_list_value (bytes_2)) = y_2)) (PreH25 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH26 : ((u8_list_value (bytes)) = x_2)) (PreH27 : (x_2 < SM2_P_Z)) (PreH28 : (0 <= x_2)) (PreH29 : (y_2 < SM2_P_Z)) (PreH30 : (0 <= y_2)) (PreH31 : (x < SM2_P_Z)) (PreH32 : (0 <= x)) (PreH33 : (y < SM2_P_Z)) (PreH34 : (0 <= y)) (PreH35 : (SM2_A_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_A_Z)) (PreH37 : (SM2_B_Z < SM2_P_Z)) (PreH38 : (0 <= SM2_B_Z)) (PreH39 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH40 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH41 : (y_2 = (sm2_point_y (P)))) (PreH42 : (x_2 = (sm2_point_x (P)))) (PreH43 : (afpoint_represents x_2 y_2 P )) (PreH44 : (afpoint_represents x y SM2_G_POINT )) (PreH45 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH46 : (id_len_pre <= 50)) (PreH47 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_28 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (u8_list_bounded (rev (bytes_6)) )) (PreH2 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH3 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_6)) = 32)) (PreH5 : (u8_list_bounded bytes_6 )) (PreH6 : (u8_list_bounded (rev (bytes_5)) )) (PreH7 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH8 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_5)) = 32)) (PreH10 : (u8_list_bounded bytes_5 )) (PreH11 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH12 : ((Zlength (ID)) = id_len_pre)) (PreH13 : (u8_list_bounded ID )) (PreH14 : ((2 + id_len_pre ) <= 250)) (PreH15 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH16 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH17 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH18 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH20 : ((u8_list_value (bytes_4)) = y)) (PreH21 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH22 : ((u8_list_value (bytes_3)) = x)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH24 : ((u8_list_value (bytes_2)) = y_2)) (PreH25 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH26 : ((u8_list_value (bytes)) = x_2)) (PreH27 : (x_2 < SM2_P_Z)) (PreH28 : (0 <= x_2)) (PreH29 : (y_2 < SM2_P_Z)) (PreH30 : (0 <= y_2)) (PreH31 : (x < SM2_P_Z)) (PreH32 : (0 <= x)) (PreH33 : (y < SM2_P_Z)) (PreH34 : (0 <= y)) (PreH35 : (SM2_A_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_A_Z)) (PreH37 : (SM2_B_Z < SM2_P_Z)) (PreH38 : (0 <= SM2_B_Z)) (PreH39 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH40 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH41 : (y_2 = (sm2_point_y (P)))) (PreH42 : (x_2 = (sm2_point_x (P)))) (PreH43 : (afpoint_represents x_2 y_2 P )) (PreH44 : (afpoint_represents x y SM2_G_POINT )) (PreH45 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH46 : (id_len_pre <= 50)) (PreH47 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm2_get_id_digest_safety_wit_29 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (u8_list_bounded (rev (bytes_6)) )) (PreH2 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH3 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_6)) = 32)) (PreH5 : (u8_list_bounded bytes_6 )) (PreH6 : (u8_list_bounded (rev (bytes_5)) )) (PreH7 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH8 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_5)) = 32)) (PreH10 : (u8_list_bounded bytes_5 )) (PreH11 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH12 : ((Zlength (ID)) = id_len_pre)) (PreH13 : (u8_list_bounded ID )) (PreH14 : ((2 + id_len_pre ) <= 250)) (PreH15 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH16 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH17 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH18 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH20 : ((u8_list_value (bytes_4)) = y)) (PreH21 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH22 : ((u8_list_value (bytes_3)) = x)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH24 : ((u8_list_value (bytes_2)) = y_2)) (PreH25 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH26 : ((u8_list_value (bytes)) = x_2)) (PreH27 : (x_2 < SM2_P_Z)) (PreH28 : (0 <= x_2)) (PreH29 : (y_2 < SM2_P_Z)) (PreH30 : (0 <= y_2)) (PreH31 : (x < SM2_P_Z)) (PreH32 : (0 <= x)) (PreH33 : (y < SM2_P_Z)) (PreH34 : (0 <= y)) (PreH35 : (SM2_A_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_A_Z)) (PreH37 : (SM2_B_Z < SM2_P_Z)) (PreH38 : (0 <= SM2_B_Z)) (PreH39 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH40 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH41 : (y_2 = (sm2_point_y (P)))) (PreH42 : (x_2 = (sm2_point_x (P)))) (PreH43 : (afpoint_represents x_2 y_2 P )) (PreH44 : (afpoint_represents x y SM2_G_POINT )) (PreH45 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH46 : (id_len_pre <= 50)) (PreH47 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_30 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_3)) = 32)) (PreH3 : (u8_list_bounded bytes_3 )) (PreH4 : (u8_list_bounded (rev (bytes_6)) )) (PreH5 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH6 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_6)) = 32)) (PreH8 : (u8_list_bounded bytes_6 )) (PreH9 : (u8_list_bounded (rev (bytes_5)) )) (PreH10 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH11 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_5)) = 32)) (PreH13 : (u8_list_bounded bytes_5 )) (PreH14 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH15 : ((Zlength (ID)) = id_len_pre)) (PreH16 : (u8_list_bounded ID )) (PreH17 : ((2 + id_len_pre ) <= 250)) (PreH18 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH19 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH20 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH21 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH22 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH23 : ((u8_list_value (bytes_4)) = y)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH25 : ((u8_list_value (bytes_3)) = x)) (PreH26 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH27 : ((u8_list_value (bytes_2)) = y_2)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH29 : ((u8_list_value (bytes)) = x_2)) (PreH30 : (x_2 < SM2_P_Z)) (PreH31 : (0 <= x_2)) (PreH32 : (y_2 < SM2_P_Z)) (PreH33 : (0 <= y_2)) (PreH34 : (x < SM2_P_Z)) (PreH35 : (0 <= x)) (PreH36 : (y < SM2_P_Z)) (PreH37 : (0 <= y)) (PreH38 : (SM2_A_Z < SM2_P_Z)) (PreH39 : (0 <= SM2_A_Z)) (PreH40 : (SM2_B_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_B_Z)) (PreH42 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH43 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH44 : (y_2 = (sm2_point_y (P)))) (PreH45 : (x_2 = (sm2_point_x (P)))) (PreH46 : (afpoint_represents x_2 y_2 P )) (PreH47 : (afpoint_represents x y SM2_G_POINT )) (PreH48 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH49 : (id_len_pre <= 50)) (PreH50 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) bytes_3 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_31 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_3)) = 32)) (PreH3 : (u8_list_bounded bytes_3 )) (PreH4 : (u8_list_bounded (rev (bytes_6)) )) (PreH5 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH6 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_6)) = 32)) (PreH8 : (u8_list_bounded bytes_6 )) (PreH9 : (u8_list_bounded (rev (bytes_5)) )) (PreH10 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH11 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_5)) = 32)) (PreH13 : (u8_list_bounded bytes_5 )) (PreH14 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH15 : ((Zlength (ID)) = id_len_pre)) (PreH16 : (u8_list_bounded ID )) (PreH17 : ((2 + id_len_pre ) <= 250)) (PreH18 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH19 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH20 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH21 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH22 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH23 : ((u8_list_value (bytes_4)) = y)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH25 : ((u8_list_value (bytes_3)) = x)) (PreH26 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH27 : ((u8_list_value (bytes_2)) = y_2)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH29 : ((u8_list_value (bytes)) = x_2)) (PreH30 : (x_2 < SM2_P_Z)) (PreH31 : (0 <= x_2)) (PreH32 : (y_2 < SM2_P_Z)) (PreH33 : (0 <= y_2)) (PreH34 : (x < SM2_P_Z)) (PreH35 : (0 <= x)) (PreH36 : (y < SM2_P_Z)) (PreH37 : (0 <= y)) (PreH38 : (SM2_A_Z < SM2_P_Z)) (PreH39 : (0 <= SM2_A_Z)) (PreH40 : (SM2_B_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_B_Z)) (PreH42 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH43 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH44 : (y_2 = (sm2_point_y (P)))) (PreH45 : (x_2 = (sm2_point_x (P)))) (PreH46 : (afpoint_represents x_2 y_2 P )) (PreH47 : (afpoint_represents x y SM2_G_POINT )) (PreH48 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH49 : (id_len_pre <= 50)) (PreH50 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) bytes_3 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (64 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 64) ”
.

Definition sm2_get_id_digest_safety_wit_32 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_3)) = 32)) (PreH3 : (u8_list_bounded bytes_3 )) (PreH4 : (u8_list_bounded (rev (bytes_6)) )) (PreH5 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH6 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_6)) = 32)) (PreH8 : (u8_list_bounded bytes_6 )) (PreH9 : (u8_list_bounded (rev (bytes_5)) )) (PreH10 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH11 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_5)) = 32)) (PreH13 : (u8_list_bounded bytes_5 )) (PreH14 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH15 : ((Zlength (ID)) = id_len_pre)) (PreH16 : (u8_list_bounded ID )) (PreH17 : ((2 + id_len_pre ) <= 250)) (PreH18 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH19 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH20 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH21 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH22 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH23 : ((u8_list_value (bytes_4)) = y)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH25 : ((u8_list_value (bytes_3)) = x)) (PreH26 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH27 : ((u8_list_value (bytes_2)) = y_2)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH29 : ((u8_list_value (bytes)) = x_2)) (PreH30 : (x_2 < SM2_P_Z)) (PreH31 : (0 <= x_2)) (PreH32 : (y_2 < SM2_P_Z)) (PreH33 : (0 <= y_2)) (PreH34 : (x < SM2_P_Z)) (PreH35 : (0 <= x)) (PreH36 : (y < SM2_P_Z)) (PreH37 : (0 <= y)) (PreH38 : (SM2_A_Z < SM2_P_Z)) (PreH39 : (0 <= SM2_A_Z)) (PreH40 : (SM2_B_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_B_Z)) (PreH42 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH43 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH44 : (y_2 = (sm2_point_y (P)))) (PreH45 : (x_2 = (sm2_point_x (P)))) (PreH46 : (afpoint_represents x_2 y_2 P )) (PreH47 : (afpoint_represents x y SM2_G_POINT )) (PreH48 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH49 : (id_len_pre <= 50)) (PreH50 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) bytes_3 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_33 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (u8_list_bounded (rev (bytes_3)) )) (PreH2 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH3 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_3)) = 32)) (PreH5 : (u8_list_bounded bytes_3 )) (PreH6 : (u8_list_bounded (rev (bytes_6)) )) (PreH7 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH8 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_6)) = 32)) (PreH10 : (u8_list_bounded bytes_6 )) (PreH11 : (u8_list_bounded (rev (bytes_5)) )) (PreH12 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH13 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_5)) = 32)) (PreH15 : (u8_list_bounded bytes_5 )) (PreH16 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH17 : ((Zlength (ID)) = id_len_pre)) (PreH18 : (u8_list_bounded ID )) (PreH19 : ((2 + id_len_pre ) <= 250)) (PreH20 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH21 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH22 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH23 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH25 : ((u8_list_value (bytes_4)) = y)) (PreH26 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH27 : ((u8_list_value (bytes_3)) = x)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH29 : ((u8_list_value (bytes_2)) = y_2)) (PreH30 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH31 : ((u8_list_value (bytes)) = x_2)) (PreH32 : (x_2 < SM2_P_Z)) (PreH33 : (0 <= x_2)) (PreH34 : (y_2 < SM2_P_Z)) (PreH35 : (0 <= y_2)) (PreH36 : (x < SM2_P_Z)) (PreH37 : (0 <= x)) (PreH38 : (y < SM2_P_Z)) (PreH39 : (0 <= y)) (PreH40 : (SM2_A_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_A_Z)) (PreH42 : (SM2_B_Z < SM2_P_Z)) (PreH43 : (0 <= SM2_B_Z)) (PreH44 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH45 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH46 : (y_2 = (sm2_point_y (P)))) (PreH47 : (x_2 = (sm2_point_x (P)))) (PreH48 : (afpoint_represents x_2 y_2 P )) (PreH49 : (afpoint_represents x y SM2_G_POINT )) (PreH50 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH51 : (id_len_pre <= 50)) (PreH52 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_34 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (u8_list_bounded (rev (bytes_3)) )) (PreH2 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH3 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_3)) = 32)) (PreH5 : (u8_list_bounded bytes_3 )) (PreH6 : (u8_list_bounded (rev (bytes_6)) )) (PreH7 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH8 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_6)) = 32)) (PreH10 : (u8_list_bounded bytes_6 )) (PreH11 : (u8_list_bounded (rev (bytes_5)) )) (PreH12 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH13 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_5)) = 32)) (PreH15 : (u8_list_bounded bytes_5 )) (PreH16 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH17 : ((Zlength (ID)) = id_len_pre)) (PreH18 : (u8_list_bounded ID )) (PreH19 : ((2 + id_len_pre ) <= 250)) (PreH20 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH21 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH22 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH23 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH25 : ((u8_list_value (bytes_4)) = y)) (PreH26 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH27 : ((u8_list_value (bytes_3)) = x)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH29 : ((u8_list_value (bytes_2)) = y_2)) (PreH30 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH31 : ((u8_list_value (bytes)) = x_2)) (PreH32 : (x_2 < SM2_P_Z)) (PreH33 : (0 <= x_2)) (PreH34 : (y_2 < SM2_P_Z)) (PreH35 : (0 <= y_2)) (PreH36 : (x < SM2_P_Z)) (PreH37 : (0 <= x)) (PreH38 : (y < SM2_P_Z)) (PreH39 : (0 <= y)) (PreH40 : (SM2_A_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_A_Z)) (PreH42 : (SM2_B_Z < SM2_P_Z)) (PreH43 : (0 <= SM2_B_Z)) (PreH44 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH45 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH46 : (y_2 = (sm2_point_y (P)))) (PreH47 : (x_2 = (sm2_point_x (P)))) (PreH48 : (afpoint_represents x_2 y_2 P )) (PreH49 : (afpoint_represents x y SM2_G_POINT )) (PreH50 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH51 : (id_len_pre <= 50)) (PreH52 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (96 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 96) ”
.

Definition sm2_get_id_digest_safety_wit_35 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (u8_list_bounded (rev (bytes_3)) )) (PreH2 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH3 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_3)) = 32)) (PreH5 : (u8_list_bounded bytes_3 )) (PreH6 : (u8_list_bounded (rev (bytes_6)) )) (PreH7 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH8 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_6)) = 32)) (PreH10 : (u8_list_bounded bytes_6 )) (PreH11 : (u8_list_bounded (rev (bytes_5)) )) (PreH12 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH13 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_5)) = 32)) (PreH15 : (u8_list_bounded bytes_5 )) (PreH16 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH17 : ((Zlength (ID)) = id_len_pre)) (PreH18 : (u8_list_bounded ID )) (PreH19 : ((2 + id_len_pre ) <= 250)) (PreH20 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH21 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH22 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH23 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH25 : ((u8_list_value (bytes_4)) = y)) (PreH26 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH27 : ((u8_list_value (bytes_3)) = x)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH29 : ((u8_list_value (bytes_2)) = y_2)) (PreH30 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH31 : ((u8_list_value (bytes)) = x_2)) (PreH32 : (x_2 < SM2_P_Z)) (PreH33 : (0 <= x_2)) (PreH34 : (y_2 < SM2_P_Z)) (PreH35 : (0 <= y_2)) (PreH36 : (x < SM2_P_Z)) (PreH37 : (0 <= x)) (PreH38 : (y < SM2_P_Z)) (PreH39 : (0 <= y)) (PreH40 : (SM2_A_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_A_Z)) (PreH42 : (SM2_B_Z < SM2_P_Z)) (PreH43 : (0 <= SM2_B_Z)) (PreH44 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH45 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH46 : (y_2 = (sm2_point_y (P)))) (PreH47 : (x_2 = (sm2_point_x (P)))) (PreH48 : (afpoint_represents x_2 y_2 P )) (PreH49 : (afpoint_represents x y SM2_G_POINT )) (PreH50 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH51 : (id_len_pre <= 50)) (PreH52 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_36 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_4)) = 32)) (PreH3 : (u8_list_bounded bytes_4 )) (PreH4 : (u8_list_bounded (rev (bytes_3)) )) (PreH5 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH6 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_3)) = 32)) (PreH8 : (u8_list_bounded bytes_3 )) (PreH9 : (u8_list_bounded (rev (bytes_6)) )) (PreH10 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH11 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_6)) = 32)) (PreH13 : (u8_list_bounded bytes_6 )) (PreH14 : (u8_list_bounded (rev (bytes_5)) )) (PreH15 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH16 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_5)) = 32)) (PreH18 : (u8_list_bounded bytes_5 )) (PreH19 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH20 : ((Zlength (ID)) = id_len_pre)) (PreH21 : (u8_list_bounded ID )) (PreH22 : ((2 + id_len_pre ) <= 250)) (PreH23 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH24 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH25 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH26 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH27 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH28 : ((u8_list_value (bytes_4)) = y)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH30 : ((u8_list_value (bytes_3)) = x)) (PreH31 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH32 : ((u8_list_value (bytes_2)) = y_2)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH34 : ((u8_list_value (bytes)) = x_2)) (PreH35 : (x_2 < SM2_P_Z)) (PreH36 : (0 <= x_2)) (PreH37 : (y_2 < SM2_P_Z)) (PreH38 : (0 <= y_2)) (PreH39 : (x < SM2_P_Z)) (PreH40 : (0 <= x)) (PreH41 : (y < SM2_P_Z)) (PreH42 : (0 <= y)) (PreH43 : (SM2_A_Z < SM2_P_Z)) (PreH44 : (0 <= SM2_A_Z)) (PreH45 : (SM2_B_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_B_Z)) (PreH47 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH48 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH49 : (y_2 = (sm2_point_y (P)))) (PreH50 : (x_2 = (sm2_point_x (P)))) (PreH51 : (afpoint_represents x_2 y_2 P )) (PreH52 : (afpoint_represents x y SM2_G_POINT )) (PreH53 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH54 : (id_len_pre <= 50)) (PreH55 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) bytes_4 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_37 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_4)) = 32)) (PreH3 : (u8_list_bounded bytes_4 )) (PreH4 : (u8_list_bounded (rev (bytes_3)) )) (PreH5 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH6 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_3)) = 32)) (PreH8 : (u8_list_bounded bytes_3 )) (PreH9 : (u8_list_bounded (rev (bytes_6)) )) (PreH10 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH11 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_6)) = 32)) (PreH13 : (u8_list_bounded bytes_6 )) (PreH14 : (u8_list_bounded (rev (bytes_5)) )) (PreH15 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH16 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_5)) = 32)) (PreH18 : (u8_list_bounded bytes_5 )) (PreH19 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH20 : ((Zlength (ID)) = id_len_pre)) (PreH21 : (u8_list_bounded ID )) (PreH22 : ((2 + id_len_pre ) <= 250)) (PreH23 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH24 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH25 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH26 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH27 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH28 : ((u8_list_value (bytes_4)) = y)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH30 : ((u8_list_value (bytes_3)) = x)) (PreH31 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH32 : ((u8_list_value (bytes_2)) = y_2)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH34 : ((u8_list_value (bytes)) = x_2)) (PreH35 : (x_2 < SM2_P_Z)) (PreH36 : (0 <= x_2)) (PreH37 : (y_2 < SM2_P_Z)) (PreH38 : (0 <= y_2)) (PreH39 : (x < SM2_P_Z)) (PreH40 : (0 <= x)) (PreH41 : (y < SM2_P_Z)) (PreH42 : (0 <= y)) (PreH43 : (SM2_A_Z < SM2_P_Z)) (PreH44 : (0 <= SM2_A_Z)) (PreH45 : (SM2_B_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_B_Z)) (PreH47 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH48 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH49 : (y_2 = (sm2_point_y (P)))) (PreH50 : (x_2 = (sm2_point_x (P)))) (PreH51 : (afpoint_represents x_2 y_2 P )) (PreH52 : (afpoint_represents x y SM2_G_POINT )) (PreH53 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH54 : (id_len_pre <= 50)) (PreH55 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) bytes_4 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (96 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 96) ”
.

Definition sm2_get_id_digest_safety_wit_38 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_4)) = 32)) (PreH3 : (u8_list_bounded bytes_4 )) (PreH4 : (u8_list_bounded (rev (bytes_3)) )) (PreH5 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH6 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_3)) = 32)) (PreH8 : (u8_list_bounded bytes_3 )) (PreH9 : (u8_list_bounded (rev (bytes_6)) )) (PreH10 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH11 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_6)) = 32)) (PreH13 : (u8_list_bounded bytes_6 )) (PreH14 : (u8_list_bounded (rev (bytes_5)) )) (PreH15 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH16 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_5)) = 32)) (PreH18 : (u8_list_bounded bytes_5 )) (PreH19 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH20 : ((Zlength (ID)) = id_len_pre)) (PreH21 : (u8_list_bounded ID )) (PreH22 : ((2 + id_len_pre ) <= 250)) (PreH23 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH24 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH25 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH26 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH27 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH28 : ((u8_list_value (bytes_4)) = y)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH30 : ((u8_list_value (bytes_3)) = x)) (PreH31 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH32 : ((u8_list_value (bytes_2)) = y_2)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH34 : ((u8_list_value (bytes)) = x_2)) (PreH35 : (x_2 < SM2_P_Z)) (PreH36 : (0 <= x_2)) (PreH37 : (y_2 < SM2_P_Z)) (PreH38 : (0 <= y_2)) (PreH39 : (x < SM2_P_Z)) (PreH40 : (0 <= x)) (PreH41 : (y < SM2_P_Z)) (PreH42 : (0 <= y)) (PreH43 : (SM2_A_Z < SM2_P_Z)) (PreH44 : (0 <= SM2_A_Z)) (PreH45 : (SM2_B_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_B_Z)) (PreH47 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH48 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH49 : (y_2 = (sm2_point_y (P)))) (PreH50 : (x_2 = (sm2_point_x (P)))) (PreH51 : (afpoint_represents x_2 y_2 P )) (PreH52 : (afpoint_represents x y SM2_G_POINT )) (PreH53 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH54 : (id_len_pre <= 50)) (PreH55 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) bytes_4 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_39 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (u8_list_bounded (rev (bytes_4)) )) (PreH2 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH3 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_4)) = 32)) (PreH5 : (u8_list_bounded bytes_4 )) (PreH6 : (u8_list_bounded (rev (bytes_3)) )) (PreH7 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH8 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_3)) = 32)) (PreH10 : (u8_list_bounded bytes_3 )) (PreH11 : (u8_list_bounded (rev (bytes_6)) )) (PreH12 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH13 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_6)) = 32)) (PreH15 : (u8_list_bounded bytes_6 )) (PreH16 : (u8_list_bounded (rev (bytes_5)) )) (PreH17 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH18 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_5)) = 32)) (PreH20 : (u8_list_bounded bytes_5 )) (PreH21 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH22 : ((Zlength (ID)) = id_len_pre)) (PreH23 : (u8_list_bounded ID )) (PreH24 : ((2 + id_len_pre ) <= 250)) (PreH25 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH26 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH27 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH28 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH30 : ((u8_list_value (bytes_4)) = y)) (PreH31 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH32 : ((u8_list_value (bytes_3)) = x)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH34 : ((u8_list_value (bytes_2)) = y_2)) (PreH35 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH36 : ((u8_list_value (bytes)) = x_2)) (PreH37 : (x_2 < SM2_P_Z)) (PreH38 : (0 <= x_2)) (PreH39 : (y_2 < SM2_P_Z)) (PreH40 : (0 <= y_2)) (PreH41 : (x < SM2_P_Z)) (PreH42 : (0 <= x)) (PreH43 : (y < SM2_P_Z)) (PreH44 : (0 <= y)) (PreH45 : (SM2_A_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_A_Z)) (PreH47 : (SM2_B_Z < SM2_P_Z)) (PreH48 : (0 <= SM2_B_Z)) (PreH49 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH50 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH51 : (y_2 = (sm2_point_y (P)))) (PreH52 : (x_2 = (sm2_point_x (P)))) (PreH53 : (afpoint_represents x_2 y_2 P )) (PreH54 : (afpoint_represents x y SM2_G_POINT )) (PreH55 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH56 : (id_len_pre <= 50)) (PreH57 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_40 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (u8_list_bounded (rev (bytes_4)) )) (PreH2 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH3 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_4)) = 32)) (PreH5 : (u8_list_bounded bytes_4 )) (PreH6 : (u8_list_bounded (rev (bytes_3)) )) (PreH7 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH8 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_3)) = 32)) (PreH10 : (u8_list_bounded bytes_3 )) (PreH11 : (u8_list_bounded (rev (bytes_6)) )) (PreH12 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH13 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_6)) = 32)) (PreH15 : (u8_list_bounded bytes_6 )) (PreH16 : (u8_list_bounded (rev (bytes_5)) )) (PreH17 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH18 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_5)) = 32)) (PreH20 : (u8_list_bounded bytes_5 )) (PreH21 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH22 : ((Zlength (ID)) = id_len_pre)) (PreH23 : (u8_list_bounded ID )) (PreH24 : ((2 + id_len_pre ) <= 250)) (PreH25 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH26 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH27 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH28 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH30 : ((u8_list_value (bytes_4)) = y)) (PreH31 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH32 : ((u8_list_value (bytes_3)) = x)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH34 : ((u8_list_value (bytes_2)) = y_2)) (PreH35 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH36 : ((u8_list_value (bytes)) = x_2)) (PreH37 : (x_2 < SM2_P_Z)) (PreH38 : (0 <= x_2)) (PreH39 : (y_2 < SM2_P_Z)) (PreH40 : (0 <= y_2)) (PreH41 : (x < SM2_P_Z)) (PreH42 : (0 <= x)) (PreH43 : (y < SM2_P_Z)) (PreH44 : (0 <= y)) (PreH45 : (SM2_A_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_A_Z)) (PreH47 : (SM2_B_Z < SM2_P_Z)) (PreH48 : (0 <= SM2_B_Z)) (PreH49 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH50 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH51 : (y_2 = (sm2_point_y (P)))) (PreH52 : (x_2 = (sm2_point_x (P)))) (PreH53 : (afpoint_represents x_2 y_2 P )) (PreH54 : (afpoint_represents x y SM2_G_POINT )) (PreH55 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH56 : (id_len_pre <= 50)) (PreH57 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (128 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 128) ”
.

Definition sm2_get_id_digest_safety_wit_41 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (u8_list_bounded (rev (bytes_4)) )) (PreH2 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH3 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_4)) = 32)) (PreH5 : (u8_list_bounded bytes_4 )) (PreH6 : (u8_list_bounded (rev (bytes_3)) )) (PreH7 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH8 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_3)) = 32)) (PreH10 : (u8_list_bounded bytes_3 )) (PreH11 : (u8_list_bounded (rev (bytes_6)) )) (PreH12 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH13 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_6)) = 32)) (PreH15 : (u8_list_bounded bytes_6 )) (PreH16 : (u8_list_bounded (rev (bytes_5)) )) (PreH17 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH18 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_5)) = 32)) (PreH20 : (u8_list_bounded bytes_5 )) (PreH21 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH22 : ((Zlength (ID)) = id_len_pre)) (PreH23 : (u8_list_bounded ID )) (PreH24 : ((2 + id_len_pre ) <= 250)) (PreH25 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH26 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH27 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH28 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH30 : ((u8_list_value (bytes_4)) = y)) (PreH31 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH32 : ((u8_list_value (bytes_3)) = x)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH34 : ((u8_list_value (bytes_2)) = y_2)) (PreH35 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH36 : ((u8_list_value (bytes)) = x_2)) (PreH37 : (x_2 < SM2_P_Z)) (PreH38 : (0 <= x_2)) (PreH39 : (y_2 < SM2_P_Z)) (PreH40 : (0 <= y_2)) (PreH41 : (x < SM2_P_Z)) (PreH42 : (0 <= x)) (PreH43 : (y < SM2_P_Z)) (PreH44 : (0 <= y)) (PreH45 : (SM2_A_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_A_Z)) (PreH47 : (SM2_B_Z < SM2_P_Z)) (PreH48 : (0 <= SM2_B_Z)) (PreH49 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH50 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH51 : (y_2 = (sm2_point_y (P)))) (PreH52 : (x_2 = (sm2_point_x (P)))) (PreH53 : (afpoint_represents x_2 y_2 P )) (PreH54 : (afpoint_represents x y SM2_G_POINT )) (PreH55 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH56 : (id_len_pre <= 50)) (PreH57 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_42 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes)) = 32)) (PreH3 : (u8_list_bounded bytes )) (PreH4 : (u8_list_bounded (rev (bytes_4)) )) (PreH5 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH6 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_4)) = 32)) (PreH8 : (u8_list_bounded bytes_4 )) (PreH9 : (u8_list_bounded (rev (bytes_3)) )) (PreH10 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH11 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_3)) = 32)) (PreH13 : (u8_list_bounded bytes_3 )) (PreH14 : (u8_list_bounded (rev (bytes_6)) )) (PreH15 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH16 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_6)) = 32)) (PreH18 : (u8_list_bounded bytes_6 )) (PreH19 : (u8_list_bounded (rev (bytes_5)) )) (PreH20 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH21 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_5)) = 32)) (PreH23 : (u8_list_bounded bytes_5 )) (PreH24 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH25 : ((Zlength (ID)) = id_len_pre)) (PreH26 : (u8_list_bounded ID )) (PreH27 : ((2 + id_len_pre ) <= 250)) (PreH28 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH29 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH30 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH31 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH32 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH33 : ((u8_list_value (bytes_4)) = y)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH35 : ((u8_list_value (bytes_3)) = x)) (PreH36 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH37 : ((u8_list_value (bytes_2)) = y_2)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH39 : ((u8_list_value (bytes)) = x_2)) (PreH40 : (x_2 < SM2_P_Z)) (PreH41 : (0 <= x_2)) (PreH42 : (y_2 < SM2_P_Z)) (PreH43 : (0 <= y_2)) (PreH44 : (x < SM2_P_Z)) (PreH45 : (0 <= x)) (PreH46 : (y < SM2_P_Z)) (PreH47 : (0 <= y)) (PreH48 : (SM2_A_Z < SM2_P_Z)) (PreH49 : (0 <= SM2_A_Z)) (PreH50 : (SM2_B_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_B_Z)) (PreH52 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH53 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH54 : (y_2 = (sm2_point_y (P)))) (PreH55 : (x_2 = (sm2_point_x (P)))) (PreH56 : (afpoint_represents x_2 y_2 P )) (PreH57 : (afpoint_represents x y SM2_G_POINT )) (PreH58 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH59 : (id_len_pre <= 50)) (PreH60 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) bytes )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_43 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes)) = 32)) (PreH3 : (u8_list_bounded bytes )) (PreH4 : (u8_list_bounded (rev (bytes_4)) )) (PreH5 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH6 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_4)) = 32)) (PreH8 : (u8_list_bounded bytes_4 )) (PreH9 : (u8_list_bounded (rev (bytes_3)) )) (PreH10 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH11 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_3)) = 32)) (PreH13 : (u8_list_bounded bytes_3 )) (PreH14 : (u8_list_bounded (rev (bytes_6)) )) (PreH15 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH16 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_6)) = 32)) (PreH18 : (u8_list_bounded bytes_6 )) (PreH19 : (u8_list_bounded (rev (bytes_5)) )) (PreH20 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH21 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_5)) = 32)) (PreH23 : (u8_list_bounded bytes_5 )) (PreH24 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH25 : ((Zlength (ID)) = id_len_pre)) (PreH26 : (u8_list_bounded ID )) (PreH27 : ((2 + id_len_pre ) <= 250)) (PreH28 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH29 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH30 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH31 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH32 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH33 : ((u8_list_value (bytes_4)) = y)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH35 : ((u8_list_value (bytes_3)) = x)) (PreH36 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH37 : ((u8_list_value (bytes_2)) = y_2)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH39 : ((u8_list_value (bytes)) = x_2)) (PreH40 : (x_2 < SM2_P_Z)) (PreH41 : (0 <= x_2)) (PreH42 : (y_2 < SM2_P_Z)) (PreH43 : (0 <= y_2)) (PreH44 : (x < SM2_P_Z)) (PreH45 : (0 <= x)) (PreH46 : (y < SM2_P_Z)) (PreH47 : (0 <= y)) (PreH48 : (SM2_A_Z < SM2_P_Z)) (PreH49 : (0 <= SM2_A_Z)) (PreH50 : (SM2_B_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_B_Z)) (PreH52 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH53 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH54 : (y_2 = (sm2_point_y (P)))) (PreH55 : (x_2 = (sm2_point_x (P)))) (PreH56 : (afpoint_represents x_2 y_2 P )) (PreH57 : (afpoint_represents x y SM2_G_POINT )) (PreH58 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH59 : (id_len_pre <= 50)) (PreH60 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) bytes )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (128 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 128) ”
.

Definition sm2_get_id_digest_safety_wit_44 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes)) = 32)) (PreH3 : (u8_list_bounded bytes )) (PreH4 : (u8_list_bounded (rev (bytes_4)) )) (PreH5 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH6 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_4)) = 32)) (PreH8 : (u8_list_bounded bytes_4 )) (PreH9 : (u8_list_bounded (rev (bytes_3)) )) (PreH10 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH11 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_3)) = 32)) (PreH13 : (u8_list_bounded bytes_3 )) (PreH14 : (u8_list_bounded (rev (bytes_6)) )) (PreH15 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH16 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_6)) = 32)) (PreH18 : (u8_list_bounded bytes_6 )) (PreH19 : (u8_list_bounded (rev (bytes_5)) )) (PreH20 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH21 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_5)) = 32)) (PreH23 : (u8_list_bounded bytes_5 )) (PreH24 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH25 : ((Zlength (ID)) = id_len_pre)) (PreH26 : (u8_list_bounded ID )) (PreH27 : ((2 + id_len_pre ) <= 250)) (PreH28 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH29 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH30 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH31 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH32 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH33 : ((u8_list_value (bytes_4)) = y)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH35 : ((u8_list_value (bytes_3)) = x)) (PreH36 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH37 : ((u8_list_value (bytes_2)) = y_2)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH39 : ((u8_list_value (bytes)) = x_2)) (PreH40 : (x_2 < SM2_P_Z)) (PreH41 : (0 <= x_2)) (PreH42 : (y_2 < SM2_P_Z)) (PreH43 : (0 <= y_2)) (PreH44 : (x < SM2_P_Z)) (PreH45 : (0 <= x)) (PreH46 : (y < SM2_P_Z)) (PreH47 : (0 <= y)) (PreH48 : (SM2_A_Z < SM2_P_Z)) (PreH49 : (0 <= SM2_A_Z)) (PreH50 : (SM2_B_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_B_Z)) (PreH52 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH53 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH54 : (y_2 = (sm2_point_y (P)))) (PreH55 : (x_2 = (sm2_point_x (P)))) (PreH56 : (afpoint_represents x_2 y_2 P )) (PreH57 : (afpoint_represents x y SM2_G_POINT )) (PreH58 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH59 : (id_len_pre <= 50)) (PreH60 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) bytes )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_45 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (u8_list_bounded (rev (bytes)) )) (PreH2 : ((Zlength ((rev (bytes)))) = 32)) (PreH3 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes)) = 32)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (u8_list_bounded (rev (bytes_4)) )) (PreH7 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH8 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_4)) = 32)) (PreH10 : (u8_list_bounded bytes_4 )) (PreH11 : (u8_list_bounded (rev (bytes_3)) )) (PreH12 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH13 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_3)) = 32)) (PreH15 : (u8_list_bounded bytes_3 )) (PreH16 : (u8_list_bounded (rev (bytes_6)) )) (PreH17 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH18 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_6)) = 32)) (PreH20 : (u8_list_bounded bytes_6 )) (PreH21 : (u8_list_bounded (rev (bytes_5)) )) (PreH22 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH23 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_5)) = 32)) (PreH25 : (u8_list_bounded bytes_5 )) (PreH26 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH27 : ((Zlength (ID)) = id_len_pre)) (PreH28 : (u8_list_bounded ID )) (PreH29 : ((2 + id_len_pre ) <= 250)) (PreH30 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH31 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH32 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH33 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH35 : ((u8_list_value (bytes_4)) = y)) (PreH36 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH37 : ((u8_list_value (bytes_3)) = x)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH39 : ((u8_list_value (bytes_2)) = y_2)) (PreH40 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH41 : ((u8_list_value (bytes)) = x_2)) (PreH42 : (x_2 < SM2_P_Z)) (PreH43 : (0 <= x_2)) (PreH44 : (y_2 < SM2_P_Z)) (PreH45 : (0 <= y_2)) (PreH46 : (x < SM2_P_Z)) (PreH47 : (0 <= x)) (PreH48 : (y < SM2_P_Z)) (PreH49 : (0 <= y)) (PreH50 : (SM2_A_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_A_Z)) (PreH52 : (SM2_B_Z < SM2_P_Z)) (PreH53 : (0 <= SM2_B_Z)) (PreH54 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH55 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH56 : (y_2 = (sm2_point_y (P)))) (PreH57 : (x_2 = (sm2_point_x (P)))) (PreH58 : (afpoint_represents x_2 y_2 P )) (PreH59 : (afpoint_represents x y SM2_G_POINT )) (PreH60 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH61 : (id_len_pre <= 50)) (PreH62 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_46 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (u8_list_bounded (rev (bytes)) )) (PreH2 : ((Zlength ((rev (bytes)))) = 32)) (PreH3 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes)) = 32)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (u8_list_bounded (rev (bytes_4)) )) (PreH7 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH8 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_4)) = 32)) (PreH10 : (u8_list_bounded bytes_4 )) (PreH11 : (u8_list_bounded (rev (bytes_3)) )) (PreH12 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH13 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_3)) = 32)) (PreH15 : (u8_list_bounded bytes_3 )) (PreH16 : (u8_list_bounded (rev (bytes_6)) )) (PreH17 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH18 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_6)) = 32)) (PreH20 : (u8_list_bounded bytes_6 )) (PreH21 : (u8_list_bounded (rev (bytes_5)) )) (PreH22 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH23 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_5)) = 32)) (PreH25 : (u8_list_bounded bytes_5 )) (PreH26 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH27 : ((Zlength (ID)) = id_len_pre)) (PreH28 : (u8_list_bounded ID )) (PreH29 : ((2 + id_len_pre ) <= 250)) (PreH30 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH31 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH32 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH33 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH35 : ((u8_list_value (bytes_4)) = y)) (PreH36 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH37 : ((u8_list_value (bytes_3)) = x)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH39 : ((u8_list_value (bytes_2)) = y_2)) (PreH40 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH41 : ((u8_list_value (bytes)) = x_2)) (PreH42 : (x_2 < SM2_P_Z)) (PreH43 : (0 <= x_2)) (PreH44 : (y_2 < SM2_P_Z)) (PreH45 : (0 <= y_2)) (PreH46 : (x < SM2_P_Z)) (PreH47 : (0 <= x)) (PreH48 : (y < SM2_P_Z)) (PreH49 : (0 <= y)) (PreH50 : (SM2_A_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_A_Z)) (PreH52 : (SM2_B_Z < SM2_P_Z)) (PreH53 : (0 <= SM2_B_Z)) (PreH54 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH55 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH56 : (y_2 = (sm2_point_y (P)))) (PreH57 : (x_2 = (sm2_point_x (P)))) (PreH58 : (afpoint_represents x_2 y_2 P )) (PreH59 : (afpoint_represents x y SM2_G_POINT )) (PreH60 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH61 : (id_len_pre <= 50)) (PreH62 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (160 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 160) ”
.

Definition sm2_get_id_digest_safety_wit_47 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (u8_list_bounded (rev (bytes)) )) (PreH2 : ((Zlength ((rev (bytes)))) = 32)) (PreH3 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes)) = 32)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (u8_list_bounded (rev (bytes_4)) )) (PreH7 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH8 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_4)) = 32)) (PreH10 : (u8_list_bounded bytes_4 )) (PreH11 : (u8_list_bounded (rev (bytes_3)) )) (PreH12 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH13 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_3)) = 32)) (PreH15 : (u8_list_bounded bytes_3 )) (PreH16 : (u8_list_bounded (rev (bytes_6)) )) (PreH17 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH18 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_6)) = 32)) (PreH20 : (u8_list_bounded bytes_6 )) (PreH21 : (u8_list_bounded (rev (bytes_5)) )) (PreH22 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH23 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_5)) = 32)) (PreH25 : (u8_list_bounded bytes_5 )) (PreH26 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH27 : ((Zlength (ID)) = id_len_pre)) (PreH28 : (u8_list_bounded ID )) (PreH29 : ((2 + id_len_pre ) <= 250)) (PreH30 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH31 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH32 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH33 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH35 : ((u8_list_value (bytes_4)) = y)) (PreH36 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH37 : ((u8_list_value (bytes_3)) = x)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH39 : ((u8_list_value (bytes_2)) = y_2)) (PreH40 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH41 : ((u8_list_value (bytes)) = x_2)) (PreH42 : (x_2 < SM2_P_Z)) (PreH43 : (0 <= x_2)) (PreH44 : (y_2 < SM2_P_Z)) (PreH45 : (0 <= y_2)) (PreH46 : (x < SM2_P_Z)) (PreH47 : (0 <= x)) (PreH48 : (y < SM2_P_Z)) (PreH49 : (0 <= y)) (PreH50 : (SM2_A_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_A_Z)) (PreH52 : (SM2_B_Z < SM2_P_Z)) (PreH53 : (0 <= SM2_B_Z)) (PreH54 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH55 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH56 : (y_2 = (sm2_point_y (P)))) (PreH57 : (x_2 = (sm2_point_x (P)))) (PreH58 : (afpoint_represents x_2 y_2 P )) (PreH59 : (afpoint_represents x y SM2_G_POINT )) (PreH60 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH61 : (id_len_pre <= 50)) (PreH62 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_48 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_2)) = 32)) (PreH3 : (u8_list_bounded bytes_2 )) (PreH4 : (u8_list_bounded (rev (bytes)) )) (PreH5 : ((Zlength ((rev (bytes)))) = 32)) (PreH6 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes)) = 32)) (PreH8 : (u8_list_bounded bytes )) (PreH9 : (u8_list_bounded (rev (bytes_4)) )) (PreH10 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH11 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_4)) = 32)) (PreH13 : (u8_list_bounded bytes_4 )) (PreH14 : (u8_list_bounded (rev (bytes_3)) )) (PreH15 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH16 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_3)) = 32)) (PreH18 : (u8_list_bounded bytes_3 )) (PreH19 : (u8_list_bounded (rev (bytes_6)) )) (PreH20 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH21 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_6)) = 32)) (PreH23 : (u8_list_bounded bytes_6 )) (PreH24 : (u8_list_bounded (rev (bytes_5)) )) (PreH25 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH26 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_5)) = 32)) (PreH28 : (u8_list_bounded bytes_5 )) (PreH29 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH30 : ((Zlength (ID)) = id_len_pre)) (PreH31 : (u8_list_bounded ID )) (PreH32 : ((2 + id_len_pre ) <= 250)) (PreH33 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH34 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH35 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH36 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH37 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH38 : ((u8_list_value (bytes_4)) = y)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH40 : ((u8_list_value (bytes_3)) = x)) (PreH41 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH42 : ((u8_list_value (bytes_2)) = y_2)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH44 : ((u8_list_value (bytes)) = x_2)) (PreH45 : (x_2 < SM2_P_Z)) (PreH46 : (0 <= x_2)) (PreH47 : (y_2 < SM2_P_Z)) (PreH48 : (0 <= y_2)) (PreH49 : (x < SM2_P_Z)) (PreH50 : (0 <= x)) (PreH51 : (y < SM2_P_Z)) (PreH52 : (0 <= y)) (PreH53 : (SM2_A_Z < SM2_P_Z)) (PreH54 : (0 <= SM2_A_Z)) (PreH55 : (SM2_B_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_B_Z)) (PreH57 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH58 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH59 : (y_2 = (sm2_point_y (P)))) (PreH60 : (x_2 = (sm2_point_x (P)))) (PreH61 : (afpoint_represents x_2 y_2 P )) (PreH62 : (afpoint_represents x y SM2_G_POINT )) (PreH63 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH64 : (id_len_pre <= 50)) (PreH65 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) bytes_2 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (160 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_49 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_2)) = 32)) (PreH3 : (u8_list_bounded bytes_2 )) (PreH4 : (u8_list_bounded (rev (bytes)) )) (PreH5 : ((Zlength ((rev (bytes)))) = 32)) (PreH6 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes)) = 32)) (PreH8 : (u8_list_bounded bytes )) (PreH9 : (u8_list_bounded (rev (bytes_4)) )) (PreH10 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH11 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_4)) = 32)) (PreH13 : (u8_list_bounded bytes_4 )) (PreH14 : (u8_list_bounded (rev (bytes_3)) )) (PreH15 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH16 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_3)) = 32)) (PreH18 : (u8_list_bounded bytes_3 )) (PreH19 : (u8_list_bounded (rev (bytes_6)) )) (PreH20 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH21 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_6)) = 32)) (PreH23 : (u8_list_bounded bytes_6 )) (PreH24 : (u8_list_bounded (rev (bytes_5)) )) (PreH25 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH26 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_5)) = 32)) (PreH28 : (u8_list_bounded bytes_5 )) (PreH29 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH30 : ((Zlength (ID)) = id_len_pre)) (PreH31 : (u8_list_bounded ID )) (PreH32 : ((2 + id_len_pre ) <= 250)) (PreH33 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH34 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH35 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH36 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH37 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH38 : ((u8_list_value (bytes_4)) = y)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH40 : ((u8_list_value (bytes_3)) = x)) (PreH41 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH42 : ((u8_list_value (bytes_2)) = y_2)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH44 : ((u8_list_value (bytes)) = x_2)) (PreH45 : (x_2 < SM2_P_Z)) (PreH46 : (0 <= x_2)) (PreH47 : (y_2 < SM2_P_Z)) (PreH48 : (0 <= y_2)) (PreH49 : (x < SM2_P_Z)) (PreH50 : (0 <= x)) (PreH51 : (y < SM2_P_Z)) (PreH52 : (0 <= y)) (PreH53 : (SM2_A_Z < SM2_P_Z)) (PreH54 : (0 <= SM2_A_Z)) (PreH55 : (SM2_B_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_B_Z)) (PreH57 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH58 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH59 : (y_2 = (sm2_point_y (P)))) (PreH60 : (x_2 = (sm2_point_x (P)))) (PreH61 : (afpoint_represents x_2 y_2 P )) (PreH62 : (afpoint_represents x y SM2_G_POINT )) (PreH63 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH64 : (id_len_pre <= 50)) (PreH65 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) bytes_2 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (160 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (160 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 160) ”
.

Definition sm2_get_id_digest_safety_wit_50 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_2)) = 32)) (PreH3 : (u8_list_bounded bytes_2 )) (PreH4 : (u8_list_bounded (rev (bytes)) )) (PreH5 : ((Zlength ((rev (bytes)))) = 32)) (PreH6 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes)) = 32)) (PreH8 : (u8_list_bounded bytes )) (PreH9 : (u8_list_bounded (rev (bytes_4)) )) (PreH10 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH11 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_4)) = 32)) (PreH13 : (u8_list_bounded bytes_4 )) (PreH14 : (u8_list_bounded (rev (bytes_3)) )) (PreH15 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH16 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_3)) = 32)) (PreH18 : (u8_list_bounded bytes_3 )) (PreH19 : (u8_list_bounded (rev (bytes_6)) )) (PreH20 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH21 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_6)) = 32)) (PreH23 : (u8_list_bounded bytes_6 )) (PreH24 : (u8_list_bounded (rev (bytes_5)) )) (PreH25 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH26 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_5)) = 32)) (PreH28 : (u8_list_bounded bytes_5 )) (PreH29 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH30 : ((Zlength (ID)) = id_len_pre)) (PreH31 : (u8_list_bounded ID )) (PreH32 : ((2 + id_len_pre ) <= 250)) (PreH33 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH34 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH35 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH36 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH37 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH38 : ((u8_list_value (bytes_4)) = y)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH40 : ((u8_list_value (bytes_3)) = x)) (PreH41 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH42 : ((u8_list_value (bytes_2)) = y_2)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH44 : ((u8_list_value (bytes)) = x_2)) (PreH45 : (x_2 < SM2_P_Z)) (PreH46 : (0 <= x_2)) (PreH47 : (y_2 < SM2_P_Z)) (PreH48 : (0 <= y_2)) (PreH49 : (x < SM2_P_Z)) (PreH50 : (0 <= x)) (PreH51 : (y < SM2_P_Z)) (PreH52 : (0 <= y)) (PreH53 : (SM2_A_Z < SM2_P_Z)) (PreH54 : (0 <= SM2_A_Z)) (PreH55 : (SM2_B_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_B_Z)) (PreH57 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH58 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH59 : (y_2 = (sm2_point_y (P)))) (PreH60 : (x_2 = (sm2_point_x (P)))) (PreH61 : (afpoint_represents x_2 y_2 P )) (PreH62 : (afpoint_represents x y SM2_G_POINT )) (PreH63 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH64 : (id_len_pre <= 50)) (PreH65 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) bytes_2 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (160 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition sm2_get_id_digest_safety_wit_51 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH2 : (u8_list_bounded (rev (bytes_2)) )) (PreH3 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH4 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH5 : ((Zlength (bytes_2)) = 32)) (PreH6 : (u8_list_bounded bytes_2 )) (PreH7 : (u8_list_bounded (rev (bytes)) )) (PreH8 : ((Zlength ((rev (bytes)))) = 32)) (PreH9 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes)) = 32)) (PreH11 : (u8_list_bounded bytes )) (PreH12 : (u8_list_bounded (rev (bytes_4)) )) (PreH13 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH14 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes_4)) = 32)) (PreH16 : (u8_list_bounded bytes_4 )) (PreH17 : (u8_list_bounded (rev (bytes_3)) )) (PreH18 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH19 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_3)) = 32)) (PreH21 : (u8_list_bounded bytes_3 )) (PreH22 : (u8_list_bounded (rev (bytes_6)) )) (PreH23 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH24 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_6)) = 32)) (PreH26 : (u8_list_bounded bytes_6 )) (PreH27 : (u8_list_bounded (rev (bytes_5)) )) (PreH28 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH29 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_5)) = 32)) (PreH31 : (u8_list_bounded bytes_5 )) (PreH32 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH33 : ((Zlength (ID)) = id_len_pre)) (PreH34 : (u8_list_bounded ID )) (PreH35 : ((2 + id_len_pre ) <= 250)) (PreH36 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH37 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH38 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH39 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH40 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH41 : ((u8_list_value (bytes_4)) = y)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH43 : ((u8_list_value (bytes_3)) = x)) (PreH44 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_2)) = y_2)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH47 : ((u8_list_value (bytes)) = x_2)) (PreH48 : (x_2 < SM2_P_Z)) (PreH49 : (0 <= x_2)) (PreH50 : (y_2 < SM2_P_Z)) (PreH51 : (0 <= y_2)) (PreH52 : (x < SM2_P_Z)) (PreH53 : (0 <= x)) (PreH54 : (y < SM2_P_Z)) (PreH55 : (0 <= y)) (PreH56 : (SM2_A_Z < SM2_P_Z)) (PreH57 : (0 <= SM2_A_Z)) (PreH58 : (SM2_B_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_B_Z)) (PreH60 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH61 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH62 : (y_2 = (sm2_point_y (P)))) (PreH63 : (x_2 = (sm2_point_x (P)))) (PreH64 : (afpoint_represents x_2 y_2 P )) (PreH65 : (afpoint_represents x y SM2_G_POINT )) (PreH66 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH67 : (id_len_pre <= 50)) (PreH68 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_52 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH2 : (u8_list_bounded (rev (bytes_2)) )) (PreH3 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH4 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH5 : ((Zlength (bytes_2)) = 32)) (PreH6 : (u8_list_bounded bytes_2 )) (PreH7 : (u8_list_bounded (rev (bytes)) )) (PreH8 : ((Zlength ((rev (bytes)))) = 32)) (PreH9 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes)) = 32)) (PreH11 : (u8_list_bounded bytes )) (PreH12 : (u8_list_bounded (rev (bytes_4)) )) (PreH13 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH14 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes_4)) = 32)) (PreH16 : (u8_list_bounded bytes_4 )) (PreH17 : (u8_list_bounded (rev (bytes_3)) )) (PreH18 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH19 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_3)) = 32)) (PreH21 : (u8_list_bounded bytes_3 )) (PreH22 : (u8_list_bounded (rev (bytes_6)) )) (PreH23 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH24 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_6)) = 32)) (PreH26 : (u8_list_bounded bytes_6 )) (PreH27 : (u8_list_bounded (rev (bytes_5)) )) (PreH28 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH29 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_5)) = 32)) (PreH31 : (u8_list_bounded bytes_5 )) (PreH32 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH33 : ((Zlength (ID)) = id_len_pre)) (PreH34 : (u8_list_bounded ID )) (PreH35 : ((2 + id_len_pre ) <= 250)) (PreH36 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH37 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH38 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH39 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH40 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH41 : ((u8_list_value (bytes_4)) = y)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH43 : ((u8_list_value (bytes_3)) = x)) (PreH44 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_2)) = y_2)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH47 : ((u8_list_value (bytes)) = x_2)) (PreH48 : (x_2 < SM2_P_Z)) (PreH49 : (0 <= x_2)) (PreH50 : (y_2 < SM2_P_Z)) (PreH51 : (0 <= y_2)) (PreH52 : (x < SM2_P_Z)) (PreH53 : (0 <= x)) (PreH54 : (y < SM2_P_Z)) (PreH55 : (0 <= y)) (PreH56 : (SM2_A_Z < SM2_P_Z)) (PreH57 : (0 <= SM2_A_Z)) (PreH58 : (SM2_B_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_B_Z)) (PreH60 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH61 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH62 : (y_2 = (sm2_point_y (P)))) (PreH63 : (x_2 = (sm2_point_x (P)))) (PreH64 : (afpoint_represents x_2 y_2 P )) (PreH65 : (afpoint_represents x y SM2_G_POINT )) (PreH66 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH67 : (id_len_pre <= 50)) (PreH68 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sm2_get_id_digest_safety_wit_53 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH2 : (u8_list_bounded (rev (bytes_2)) )) (PreH3 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH4 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH5 : ((Zlength (bytes_2)) = 32)) (PreH6 : (u8_list_bounded bytes_2 )) (PreH7 : (u8_list_bounded (rev (bytes)) )) (PreH8 : ((Zlength ((rev (bytes)))) = 32)) (PreH9 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes)) = 32)) (PreH11 : (u8_list_bounded bytes )) (PreH12 : (u8_list_bounded (rev (bytes_4)) )) (PreH13 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH14 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes_4)) = 32)) (PreH16 : (u8_list_bounded bytes_4 )) (PreH17 : (u8_list_bounded (rev (bytes_3)) )) (PreH18 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH19 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_3)) = 32)) (PreH21 : (u8_list_bounded bytes_3 )) (PreH22 : (u8_list_bounded (rev (bytes_6)) )) (PreH23 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH24 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_6)) = 32)) (PreH26 : (u8_list_bounded bytes_6 )) (PreH27 : (u8_list_bounded (rev (bytes_5)) )) (PreH28 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH29 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_5)) = 32)) (PreH31 : (u8_list_bounded bytes_5 )) (PreH32 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH33 : ((Zlength (ID)) = id_len_pre)) (PreH34 : (u8_list_bounded ID )) (PreH35 : ((2 + id_len_pre ) <= 250)) (PreH36 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH37 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH38 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH39 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH40 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH41 : ((u8_list_value (bytes_4)) = y)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH43 : ((u8_list_value (bytes_3)) = x)) (PreH44 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_2)) = y_2)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH47 : ((u8_list_value (bytes)) = x_2)) (PreH48 : (x_2 < SM2_P_Z)) (PreH49 : (0 <= x_2)) (PreH50 : (y_2 < SM2_P_Z)) (PreH51 : (0 <= y_2)) (PreH52 : (x < SM2_P_Z)) (PreH53 : (0 <= x)) (PreH54 : (y < SM2_P_Z)) (PreH55 : (0 <= y)) (PreH56 : (SM2_A_Z < SM2_P_Z)) (PreH57 : (0 <= SM2_A_Z)) (PreH58 : (SM2_B_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_B_Z)) (PreH60 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH61 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH62 : (y_2 = (sm2_point_y (P)))) (PreH63 : (x_2 = (sm2_point_x (P)))) (PreH64 : (afpoint_represents x_2 y_2 P )) (PreH65 : (afpoint_represents x y SM2_G_POINT )) (PreH66 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH67 : (id_len_pre <= 50)) (PreH68 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_54 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH2 : (u8_list_bounded (rev (bytes_2)) )) (PreH3 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH4 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH5 : ((Zlength (bytes_2)) = 32)) (PreH6 : (u8_list_bounded bytes_2 )) (PreH7 : (u8_list_bounded (rev (bytes)) )) (PreH8 : ((Zlength ((rev (bytes)))) = 32)) (PreH9 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes)) = 32)) (PreH11 : (u8_list_bounded bytes )) (PreH12 : (u8_list_bounded (rev (bytes_4)) )) (PreH13 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH14 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes_4)) = 32)) (PreH16 : (u8_list_bounded bytes_4 )) (PreH17 : (u8_list_bounded (rev (bytes_3)) )) (PreH18 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH19 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_3)) = 32)) (PreH21 : (u8_list_bounded bytes_3 )) (PreH22 : (u8_list_bounded (rev (bytes_6)) )) (PreH23 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH24 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_6)) = 32)) (PreH26 : (u8_list_bounded bytes_6 )) (PreH27 : (u8_list_bounded (rev (bytes_5)) )) (PreH28 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH29 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_5)) = 32)) (PreH31 : (u8_list_bounded bytes_5 )) (PreH32 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH33 : ((Zlength (ID)) = id_len_pre)) (PreH34 : (u8_list_bounded ID )) (PreH35 : ((2 + id_len_pre ) <= 250)) (PreH36 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH37 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH38 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH39 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH40 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH41 : ((u8_list_value (bytes_4)) = y)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH43 : ((u8_list_value (bytes_3)) = x)) (PreH44 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_2)) = y_2)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH47 : ((u8_list_value (bytes)) = x_2)) (PreH48 : (x_2 < SM2_P_Z)) (PreH49 : (0 <= x_2)) (PreH50 : (y_2 < SM2_P_Z)) (PreH51 : (0 <= y_2)) (PreH52 : (x < SM2_P_Z)) (PreH53 : (0 <= x)) (PreH54 : (y < SM2_P_Z)) (PreH55 : (0 <= y)) (PreH56 : (SM2_A_Z < SM2_P_Z)) (PreH57 : (0 <= SM2_A_Z)) (PreH58 : (SM2_B_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_B_Z)) (PreH60 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH61 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH62 : (y_2 = (sm2_point_y (P)))) (PreH63 : (x_2 = (sm2_point_x (P)))) (PreH64 : (afpoint_represents x_2 y_2 P )) (PreH65 : (afpoint_represents x y SM2_G_POINT )) (PreH66 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH67 : (id_len_pre <= 50)) (PreH68 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (192 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 192) ”
.

Definition sm2_get_id_digest_safety_wit_55 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_safety_wit_56 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sm2_get_id_digest_safety_wit_57 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (192 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 192) ”
.

Definition sm2_get_id_digest_safety_wit_58 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  (UCharArray.undef_full ( &( "charlist" ) ) (0 + 192 ) )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((sm2_za_input (ID) (P)))) )
  **  (store_sm3_ti )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2_get_id_digest_entail_wit_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_sm3_ti )
  **  (store_sm2_g )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_afpoint ( &( "SM2_G" ) ) SM2_G_POINT )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_3 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH2 : (id_len_pre <= 50)) (PreH3 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_afpoint ( &( "SM2_G" ) ) SM2_G_POINT )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
|--
  EX (y_2: Z)  (x_2: Z)  (y: Z)  (x: Z) ,
  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_afpoint_fields pubkey_pre x_2 y_2 )
  **  (store_afpoint_fields ( &( "SM2_G" ) ) x y )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_4 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (afpoint_represents x_2 y_2 P )) (PreH2 : (afpoint_represents x y SM2_G_POINT )) (PreH3 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH4 : (id_len_pre <= 50)) (PreH5 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_afpoint_fields pubkey_pre x_2 y_2 )
  **  (store_afpoint_fields ( &( "SM2_G" ) ) x y )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_afpoint_fields pubkey_pre x_2 y_2 )
  **  (store_afpoint_fields ( &( "SM2_G" ) ) x y )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_5 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH2 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH3 : (y_2 = (sm2_point_y (P)))) (PreH4 : (x_2 = (sm2_point_x (P)))) (PreH5 : (afpoint_represents x_2 y_2 P )) (PreH6 : (afpoint_represents x y SM2_G_POINT )) (PreH7 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH8 : (id_len_pre <= 50)) (PreH9 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_afpoint_fields pubkey_pre x_2 y_2 )
  **  (store_afpoint_fields ( &( "SM2_G" ) ) x y )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_fp &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_6 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH2 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH3 : (y_2 = (sm2_point_y (P)))) (PreH4 : (x_2 = (sm2_point_x (P)))) (PreH5 : (afpoint_represents x_2 y_2 P )) (PreH6 : (afpoint_represents x y SM2_G_POINT )) (PreH7 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH8 : (id_len_pre <= 50)) (PreH9 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_fp &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_7 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH2 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH3 : (y_2 = (sm2_point_y (P)))) (PreH4 : (x_2 = (sm2_point_x (P)))) (PreH5 : (afpoint_represents x_2 y_2 P )) (PreH6 : (afpoint_represents x y SM2_G_POINT )) (PreH7 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH8 : (id_len_pre <= 50)) (PreH9 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_sm3_ti )
  **  (store_sm2_b )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_8 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH2 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH3 : (y_2 = (sm2_point_y (P)))) (PreH4 : (x_2 = (sm2_point_x (P)))) (PreH5 : (afpoint_represents x_2 y_2 P )) (PreH6 : (afpoint_represents x y SM2_G_POINT )) (PreH7 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH8 : (id_len_pre <= 50)) (PreH9 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_fp &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_9 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (PreH1 : (x_2 < SM2_P_Z)) (PreH2 : (0 <= x_2)) (PreH3 : (y_2 < SM2_P_Z)) (PreH4 : (0 <= y_2)) (PreH5 : (x < SM2_P_Z)) (PreH6 : (0 <= x)) (PreH7 : (y < SM2_P_Z)) (PreH8 : (0 <= y)) (PreH9 : (SM2_A_Z < SM2_P_Z)) (PreH10 : (0 <= SM2_A_Z)) (PreH11 : (SM2_B_Z < SM2_P_Z)) (PreH12 : (0 <= SM2_B_Z)) (PreH13 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH14 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH15 : (y_2 = (sm2_point_y (P)))) (PreH16 : (x_2 = (sm2_point_x (P)))) (PreH17 : (afpoint_represents x_2 y_2 P )) (PreH18 : (afpoint_represents x y SM2_G_POINT )) (PreH19 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH20 : (id_len_pre <= 50)) (PreH21 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  EX (bytes_6: (@list Z))  (bytes_5: (@list Z))  (bytes_4: (@list Z))  (bytes_3: (@list Z))  (bytes_2: (@list Z))  (bytes: (@list Z)) ,
  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_10 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_11 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (replace_Znth (1) ((Some ((unsigned_last_nbits (((id_len_pre * 8 ) % ( 256 ) )) (8))))) ((replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (cons ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))) ((cons ((unsigned_last_nbits (((id_len_pre * 8 ) % ( 256 ) )) (8))) ((@nil Z))))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_12 := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (cons ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))) ((cons ((unsigned_last_nbits (((id_len_pre * 8 ) % ( 256 ) )) (8))) ((@nil Z))))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  TT && emp 
|--
  “ ((cons ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))) ((cons ((unsigned_last_nbits (((id_len_pre * 8 ) % ( 256 ) )) (8))) ((@nil Z))))) = (sm2_entla_bytes (id_len_pre))) ”
  &&  emp
).

Definition sm2_get_id_digest_entail_wit_12_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((cons ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))) ((cons ((unsigned_last_nbits (((id_len_pre * 8 ) % ( 256 ) )) (8))) ((@nil Z))))) = (sm2_entla_bytes (id_len_pre)))
.

Definition sm2_get_id_digest_entail_wit_13 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_14 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_5)) = 32)) (PreH3 : (u8_list_bounded bytes_5 )) (PreH4 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH5 : ((Zlength (ID)) = id_len_pre)) (PreH6 : (u8_list_bounded ID )) (PreH7 : ((2 + id_len_pre ) <= 250)) (PreH8 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH9 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH10 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH11 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH12 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH13 : ((u8_list_value (bytes_4)) = y)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH15 : ((u8_list_value (bytes_3)) = x)) (PreH16 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH17 : ((u8_list_value (bytes_2)) = y_2)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH19 : ((u8_list_value (bytes)) = x_2)) (PreH20 : (x_2 < SM2_P_Z)) (PreH21 : (0 <= x_2)) (PreH22 : (y_2 < SM2_P_Z)) (PreH23 : (0 <= y_2)) (PreH24 : (x < SM2_P_Z)) (PreH25 : (0 <= x)) (PreH26 : (y < SM2_P_Z)) (PreH27 : (0 <= y)) (PreH28 : (SM2_A_Z < SM2_P_Z)) (PreH29 : (0 <= SM2_A_Z)) (PreH30 : (SM2_B_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_B_Z)) (PreH32 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH33 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH34 : (y_2 = (sm2_point_y (P)))) (PreH35 : (x_2 = (sm2_point_x (P)))) (PreH36 : (afpoint_represents x_2 y_2 P )) (PreH37 : (afpoint_represents x y SM2_G_POINT )) (PreH38 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH39 : (id_len_pre <= 50)) (PreH40 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "charlist" ) ) + (0 * sizeof(UCHAR))) 32 (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_15 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_6)) = 32)) (PreH3 : (u8_list_bounded bytes_6 )) (PreH4 : (u8_list_bounded (rev (bytes_5)) )) (PreH5 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH6 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_5)) = 32)) (PreH8 : (u8_list_bounded bytes_5 )) (PreH9 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH10 : ((Zlength (ID)) = id_len_pre)) (PreH11 : (u8_list_bounded ID )) (PreH12 : ((2 + id_len_pre ) <= 250)) (PreH13 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH14 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH15 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH16 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH17 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH18 : ((u8_list_value (bytes_4)) = y)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH20 : ((u8_list_value (bytes_3)) = x)) (PreH21 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH22 : ((u8_list_value (bytes_2)) = y_2)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH24 : ((u8_list_value (bytes)) = x_2)) (PreH25 : (x_2 < SM2_P_Z)) (PreH26 : (0 <= x_2)) (PreH27 : (y_2 < SM2_P_Z)) (PreH28 : (0 <= y_2)) (PreH29 : (x < SM2_P_Z)) (PreH30 : (0 <= x)) (PreH31 : (y < SM2_P_Z)) (PreH32 : (0 <= y)) (PreH33 : (SM2_A_Z < SM2_P_Z)) (PreH34 : (0 <= SM2_A_Z)) (PreH35 : (SM2_B_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_B_Z)) (PreH37 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH38 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH39 : (y_2 = (sm2_point_y (P)))) (PreH40 : (x_2 = (sm2_point_x (P)))) (PreH41 : (afpoint_represents x_2 y_2 P )) (PreH42 : (afpoint_represents x y SM2_G_POINT )) (PreH43 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH44 : (id_len_pre <= 50)) (PreH45 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "charlist" ) ) + (32 * sizeof(UCHAR))) 32 (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_16 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_3)) = 32)) (PreH3 : (u8_list_bounded bytes_3 )) (PreH4 : (u8_list_bounded (rev (bytes_6)) )) (PreH5 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH6 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_6)) = 32)) (PreH8 : (u8_list_bounded bytes_6 )) (PreH9 : (u8_list_bounded (rev (bytes_5)) )) (PreH10 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH11 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_5)) = 32)) (PreH13 : (u8_list_bounded bytes_5 )) (PreH14 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH15 : ((Zlength (ID)) = id_len_pre)) (PreH16 : (u8_list_bounded ID )) (PreH17 : ((2 + id_len_pre ) <= 250)) (PreH18 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH19 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH20 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH21 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH22 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH23 : ((u8_list_value (bytes_4)) = y)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH25 : ((u8_list_value (bytes_3)) = x)) (PreH26 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH27 : ((u8_list_value (bytes_2)) = y_2)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH29 : ((u8_list_value (bytes)) = x_2)) (PreH30 : (x_2 < SM2_P_Z)) (PreH31 : (0 <= x_2)) (PreH32 : (y_2 < SM2_P_Z)) (PreH33 : (0 <= y_2)) (PreH34 : (x < SM2_P_Z)) (PreH35 : (0 <= x)) (PreH36 : (y < SM2_P_Z)) (PreH37 : (0 <= y)) (PreH38 : (SM2_A_Z < SM2_P_Z)) (PreH39 : (0 <= SM2_A_Z)) (PreH40 : (SM2_B_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_B_Z)) (PreH42 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH43 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH44 : (y_2 = (sm2_point_y (P)))) (PreH45 : (x_2 = (sm2_point_x (P)))) (PreH46 : (afpoint_represents x_2 y_2 P )) (PreH47 : (afpoint_represents x y SM2_G_POINT )) (PreH48 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH49 : (id_len_pre <= 50)) (PreH50 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "charlist" ) ) + (64 * sizeof(UCHAR))) 32 (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_17 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_4)) = 32)) (PreH3 : (u8_list_bounded bytes_4 )) (PreH4 : (u8_list_bounded (rev (bytes_3)) )) (PreH5 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH6 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_3)) = 32)) (PreH8 : (u8_list_bounded bytes_3 )) (PreH9 : (u8_list_bounded (rev (bytes_6)) )) (PreH10 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH11 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_6)) = 32)) (PreH13 : (u8_list_bounded bytes_6 )) (PreH14 : (u8_list_bounded (rev (bytes_5)) )) (PreH15 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH16 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_5)) = 32)) (PreH18 : (u8_list_bounded bytes_5 )) (PreH19 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH20 : ((Zlength (ID)) = id_len_pre)) (PreH21 : (u8_list_bounded ID )) (PreH22 : ((2 + id_len_pre ) <= 250)) (PreH23 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH24 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH25 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH26 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH27 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH28 : ((u8_list_value (bytes_4)) = y)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH30 : ((u8_list_value (bytes_3)) = x)) (PreH31 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH32 : ((u8_list_value (bytes_2)) = y_2)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH34 : ((u8_list_value (bytes)) = x_2)) (PreH35 : (x_2 < SM2_P_Z)) (PreH36 : (0 <= x_2)) (PreH37 : (y_2 < SM2_P_Z)) (PreH38 : (0 <= y_2)) (PreH39 : (x < SM2_P_Z)) (PreH40 : (0 <= x)) (PreH41 : (y < SM2_P_Z)) (PreH42 : (0 <= y)) (PreH43 : (SM2_A_Z < SM2_P_Z)) (PreH44 : (0 <= SM2_A_Z)) (PreH45 : (SM2_B_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_B_Z)) (PreH47 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH48 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH49 : (y_2 = (sm2_point_y (P)))) (PreH50 : (x_2 = (sm2_point_x (P)))) (PreH51 : (afpoint_represents x_2 y_2 P )) (PreH52 : (afpoint_represents x y SM2_G_POINT )) (PreH53 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH54 : (id_len_pre <= 50)) (PreH55 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "charlist" ) ) + (96 * sizeof(UCHAR))) 32 (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_18 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes)) = 32)) (PreH3 : (u8_list_bounded bytes )) (PreH4 : (u8_list_bounded (rev (bytes_4)) )) (PreH5 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH6 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_4)) = 32)) (PreH8 : (u8_list_bounded bytes_4 )) (PreH9 : (u8_list_bounded (rev (bytes_3)) )) (PreH10 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH11 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_3)) = 32)) (PreH13 : (u8_list_bounded bytes_3 )) (PreH14 : (u8_list_bounded (rev (bytes_6)) )) (PreH15 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH16 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_6)) = 32)) (PreH18 : (u8_list_bounded bytes_6 )) (PreH19 : (u8_list_bounded (rev (bytes_5)) )) (PreH20 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH21 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_5)) = 32)) (PreH23 : (u8_list_bounded bytes_5 )) (PreH24 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH25 : ((Zlength (ID)) = id_len_pre)) (PreH26 : (u8_list_bounded ID )) (PreH27 : ((2 + id_len_pre ) <= 250)) (PreH28 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH29 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH30 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH31 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH32 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH33 : ((u8_list_value (bytes_4)) = y)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH35 : ((u8_list_value (bytes_3)) = x)) (PreH36 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH37 : ((u8_list_value (bytes_2)) = y_2)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH39 : ((u8_list_value (bytes)) = x_2)) (PreH40 : (x_2 < SM2_P_Z)) (PreH41 : (0 <= x_2)) (PreH42 : (y_2 < SM2_P_Z)) (PreH43 : (0 <= y_2)) (PreH44 : (x < SM2_P_Z)) (PreH45 : (0 <= x)) (PreH46 : (y < SM2_P_Z)) (PreH47 : (0 <= y)) (PreH48 : (SM2_A_Z < SM2_P_Z)) (PreH49 : (0 <= SM2_A_Z)) (PreH50 : (SM2_B_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_B_Z)) (PreH52 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH53 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH54 : (y_2 = (sm2_point_y (P)))) (PreH55 : (x_2 = (sm2_point_x (P)))) (PreH56 : (afpoint_represents x_2 y_2 P )) (PreH57 : (afpoint_represents x y SM2_G_POINT )) (PreH58 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH59 : (id_len_pre <= 50)) (PreH60 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "charlist" ) ) + (128 * sizeof(UCHAR))) 32 (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_19 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_2)) = 32)) (PreH3 : (u8_list_bounded bytes_2 )) (PreH4 : (u8_list_bounded (rev (bytes)) )) (PreH5 : ((Zlength ((rev (bytes)))) = 32)) (PreH6 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes)) = 32)) (PreH8 : (u8_list_bounded bytes )) (PreH9 : (u8_list_bounded (rev (bytes_4)) )) (PreH10 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH11 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_4)) = 32)) (PreH13 : (u8_list_bounded bytes_4 )) (PreH14 : (u8_list_bounded (rev (bytes_3)) )) (PreH15 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH16 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_3)) = 32)) (PreH18 : (u8_list_bounded bytes_3 )) (PreH19 : (u8_list_bounded (rev (bytes_6)) )) (PreH20 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH21 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_6)) = 32)) (PreH23 : (u8_list_bounded bytes_6 )) (PreH24 : (u8_list_bounded (rev (bytes_5)) )) (PreH25 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH26 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_5)) = 32)) (PreH28 : (u8_list_bounded bytes_5 )) (PreH29 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH30 : ((Zlength (ID)) = id_len_pre)) (PreH31 : (u8_list_bounded ID )) (PreH32 : ((2 + id_len_pre ) <= 250)) (PreH33 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH34 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH35 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH36 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH37 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH38 : ((u8_list_value (bytes_4)) = y)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH40 : ((u8_list_value (bytes_3)) = x)) (PreH41 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH42 : ((u8_list_value (bytes_2)) = y_2)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH44 : ((u8_list_value (bytes)) = x_2)) (PreH45 : (x_2 < SM2_P_Z)) (PreH46 : (0 <= x_2)) (PreH47 : (y_2 < SM2_P_Z)) (PreH48 : (0 <= y_2)) (PreH49 : (x < SM2_P_Z)) (PreH50 : (0 <= x)) (PreH51 : (y < SM2_P_Z)) (PreH52 : (0 <= y)) (PreH53 : (SM2_A_Z < SM2_P_Z)) (PreH54 : (0 <= SM2_A_Z)) (PreH55 : (SM2_B_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_B_Z)) (PreH57 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH58 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH59 : (y_2 = (sm2_point_y (P)))) (PreH60 : (x_2 = (sm2_point_x (P)))) (PreH61 : (afpoint_represents x_2 y_2 P )) (PreH62 : (afpoint_represents x y SM2_G_POINT )) (PreH63 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH64 : (id_len_pre <= 50)) (PreH65 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "charlist" ) ) + (160 * sizeof(UCHAR))) 32 (rev (bytes_2)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) (rev (bytes_2)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_20 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (u8_list_bounded (rev (bytes_2)) )) (PreH2 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH3 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_2)) = 32)) (PreH5 : (u8_list_bounded bytes_2 )) (PreH6 : (u8_list_bounded (rev (bytes)) )) (PreH7 : ((Zlength ((rev (bytes)))) = 32)) (PreH8 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes)) = 32)) (PreH10 : (u8_list_bounded bytes )) (PreH11 : (u8_list_bounded (rev (bytes_4)) )) (PreH12 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH13 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_4)) = 32)) (PreH15 : (u8_list_bounded bytes_4 )) (PreH16 : (u8_list_bounded (rev (bytes_3)) )) (PreH17 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH18 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_3)) = 32)) (PreH20 : (u8_list_bounded bytes_3 )) (PreH21 : (u8_list_bounded (rev (bytes_6)) )) (PreH22 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH23 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_6)) = 32)) (PreH25 : (u8_list_bounded bytes_6 )) (PreH26 : (u8_list_bounded (rev (bytes_5)) )) (PreH27 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH28 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_5)) = 32)) (PreH30 : (u8_list_bounded bytes_5 )) (PreH31 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH32 : ((Zlength (ID)) = id_len_pre)) (PreH33 : (u8_list_bounded ID )) (PreH34 : ((2 + id_len_pre ) <= 250)) (PreH35 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH36 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH37 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH38 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH40 : ((u8_list_value (bytes_4)) = y)) (PreH41 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH42 : ((u8_list_value (bytes_3)) = x)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_2)) = y_2)) (PreH45 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH46 : ((u8_list_value (bytes)) = x_2)) (PreH47 : (x_2 < SM2_P_Z)) (PreH48 : (0 <= x_2)) (PreH49 : (y_2 < SM2_P_Z)) (PreH50 : (0 <= y_2)) (PreH51 : (x < SM2_P_Z)) (PreH52 : (0 <= x)) (PreH53 : (y < SM2_P_Z)) (PreH54 : (0 <= y)) (PreH55 : (SM2_A_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_A_Z)) (PreH57 : (SM2_B_Z < SM2_P_Z)) (PreH58 : (0 <= SM2_B_Z)) (PreH59 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH60 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH61 : (y_2 = (sm2_point_y (P)))) (PreH62 : (x_2 = (sm2_point_x (P)))) (PreH63 : (afpoint_represents x_2 y_2 P )) (PreH64 : (afpoint_represents x y SM2_G_POINT )) (PreH65 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH66 : (id_len_pre <= 50)) (PreH67 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) (rev (bytes_2)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (160 + 32 ) (app ((rev (bytes_5))) ((app ((rev (bytes_6))) ((app ((rev (bytes_3))) ((app ((rev (bytes_4))) ((app ((rev (bytes))) ((rev (bytes_2)))))))))))) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_21 := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (u8_list_bounded (rev (bytes_2)) )) (PreH2 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH3 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_2)) = 32)) (PreH5 : (u8_list_bounded bytes_2 )) (PreH6 : (u8_list_bounded (rev (bytes)) )) (PreH7 : ((Zlength ((rev (bytes)))) = 32)) (PreH8 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes)) = 32)) (PreH10 : (u8_list_bounded bytes )) (PreH11 : (u8_list_bounded (rev (bytes_4)) )) (PreH12 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH13 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_4)) = 32)) (PreH15 : (u8_list_bounded bytes_4 )) (PreH16 : (u8_list_bounded (rev (bytes_3)) )) (PreH17 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH18 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_3)) = 32)) (PreH20 : (u8_list_bounded bytes_3 )) (PreH21 : (u8_list_bounded (rev (bytes_6)) )) (PreH22 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH23 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_6)) = 32)) (PreH25 : (u8_list_bounded bytes_6 )) (PreH26 : (u8_list_bounded (rev (bytes_5)) )) (PreH27 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH28 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_5)) = 32)) (PreH30 : (u8_list_bounded bytes_5 )) (PreH31 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH32 : ((Zlength (ID)) = id_len_pre)) (PreH33 : (u8_list_bounded ID )) (PreH34 : ((2 + id_len_pre ) <= 250)) (PreH35 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH36 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH37 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH38 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH40 : ((u8_list_value (bytes_4)) = y)) (PreH41 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH42 : ((u8_list_value (bytes_3)) = x)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_2)) = y_2)) (PreH45 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH46 : ((u8_list_value (bytes)) = x_2)) (PreH47 : (x_2 < SM2_P_Z)) (PreH48 : (0 <= x_2)) (PreH49 : (y_2 < SM2_P_Z)) (PreH50 : (0 <= y_2)) (PreH51 : (x < SM2_P_Z)) (PreH52 : (0 <= x)) (PreH53 : (y < SM2_P_Z)) (PreH54 : (0 <= y)) (PreH55 : (SM2_A_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_A_Z)) (PreH57 : (SM2_B_Z < SM2_P_Z)) (PreH58 : (0 <= SM2_B_Z)) (PreH59 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH60 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH61 : (y_2 = (sm2_point_y (P)))) (PreH62 : (x_2 = (sm2_point_x (P)))) (PreH63 : (afpoint_represents x_2 y_2 P )) (PreH64 : (afpoint_represents x y SM2_G_POINT )) (PreH65 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH66 : (id_len_pre <= 50)) (PreH67 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (160 + 32 ) (app ((rev (bytes_5))) ((app ((rev (bytes_6))) ((app ((rev (bytes_3))) ((app ((rev (bytes_4))) ((app ((rev (bytes))) ((rev (bytes_2)))))))))))) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (u8_list_bounded (rev (bytes_2)) )) (PreH2 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH3 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_2)) = 32)) (PreH5 : (u8_list_bounded bytes_2 )) (PreH6 : (u8_list_bounded (rev (bytes)) )) (PreH7 : ((Zlength ((rev (bytes)))) = 32)) (PreH8 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes)) = 32)) (PreH10 : (u8_list_bounded bytes )) (PreH11 : (u8_list_bounded (rev (bytes_4)) )) (PreH12 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH13 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_4)) = 32)) (PreH15 : (u8_list_bounded bytes_4 )) (PreH16 : (u8_list_bounded (rev (bytes_3)) )) (PreH17 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH18 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_3)) = 32)) (PreH20 : (u8_list_bounded bytes_3 )) (PreH21 : (u8_list_bounded (rev (bytes_6)) )) (PreH22 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH23 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_6)) = 32)) (PreH25 : (u8_list_bounded bytes_6 )) (PreH26 : (u8_list_bounded (rev (bytes_5)) )) (PreH27 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH28 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_5)) = 32)) (PreH30 : (u8_list_bounded bytes_5 )) (PreH31 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH32 : ((Zlength (ID)) = id_len_pre)) (PreH33 : (u8_list_bounded ID )) (PreH34 : ((2 + id_len_pre ) <= 250)) (PreH35 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH36 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH37 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH38 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH40 : ((u8_list_value (bytes_4)) = y)) (PreH41 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH42 : ((u8_list_value (bytes_3)) = x)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_2)) = y_2)) (PreH45 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH46 : ((u8_list_value (bytes)) = x_2)) (PreH47 : (x_2 < SM2_P_Z)) (PreH48 : (0 <= x_2)) (PreH49 : (y_2 < SM2_P_Z)) (PreH50 : (0 <= y_2)) (PreH51 : (x < SM2_P_Z)) (PreH52 : (0 <= x)) (PreH53 : (y < SM2_P_Z)) (PreH54 : (0 <= y)) (PreH55 : (SM2_A_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_A_Z)) (PreH57 : (SM2_B_Z < SM2_P_Z)) (PreH58 : (0 <= SM2_B_Z)) (PreH59 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH60 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH61 : (y_2 = (sm2_point_y (P)))) (PreH62 : (x_2 = (sm2_point_x (P)))) (PreH63 : (afpoint_represents x_2 y_2 P )) (PreH64 : (afpoint_represents x y SM2_G_POINT )) (PreH65 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH66 : (id_len_pre <= 50)) (PreH67 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  TT && emp 
|--
  “ ((app ((rev (bytes_5))) ((app ((rev (bytes_6))) ((app ((rev (bytes_3))) ((app ((rev (bytes_4))) ((app ((rev (bytes))) ((rev (bytes_2)))))))))))) = (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2))))))))))))) ”
  &&  emp
).

Definition sm2_get_id_digest_entail_wit_21_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (u8_list_bounded (rev (bytes_2)) )) (PreH2 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH3 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_2)) = 32)) (PreH5 : (u8_list_bounded bytes_2 )) (PreH6 : (u8_list_bounded (rev (bytes)) )) (PreH7 : ((Zlength ((rev (bytes)))) = 32)) (PreH8 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes)) = 32)) (PreH10 : (u8_list_bounded bytes )) (PreH11 : (u8_list_bounded (rev (bytes_4)) )) (PreH12 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH13 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_4)) = 32)) (PreH15 : (u8_list_bounded bytes_4 )) (PreH16 : (u8_list_bounded (rev (bytes_3)) )) (PreH17 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH18 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_3)) = 32)) (PreH20 : (u8_list_bounded bytes_3 )) (PreH21 : (u8_list_bounded (rev (bytes_6)) )) (PreH22 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH23 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_6)) = 32)) (PreH25 : (u8_list_bounded bytes_6 )) (PreH26 : (u8_list_bounded (rev (bytes_5)) )) (PreH27 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH28 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_5)) = 32)) (PreH30 : (u8_list_bounded bytes_5 )) (PreH31 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH32 : ((Zlength (ID)) = id_len_pre)) (PreH33 : (u8_list_bounded ID )) (PreH34 : ((2 + id_len_pre ) <= 250)) (PreH35 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH36 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH37 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH38 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH40 : ((u8_list_value (bytes_4)) = y)) (PreH41 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH42 : ((u8_list_value (bytes_3)) = x)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_2)) = y_2)) (PreH45 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH46 : ((u8_list_value (bytes)) = x_2)) (PreH47 : (x_2 < SM2_P_Z)) (PreH48 : (0 <= x_2)) (PreH49 : (y_2 < SM2_P_Z)) (PreH50 : (0 <= y_2)) (PreH51 : (x < SM2_P_Z)) (PreH52 : (0 <= x)) (PreH53 : (y < SM2_P_Z)) (PreH54 : (0 <= y)) (PreH55 : (SM2_A_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_A_Z)) (PreH57 : (SM2_B_Z < SM2_P_Z)) (PreH58 : (0 <= SM2_B_Z)) (PreH59 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH60 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH61 : (y_2 = (sm2_point_y (P)))) (PreH62 : (x_2 = (sm2_point_x (P)))) (PreH63 : (afpoint_represents x_2 y_2 P )) (PreH64 : (afpoint_represents x y SM2_G_POINT )) (PreH65 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH66 : (id_len_pre <= 50)) (PreH67 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((app ((rev (bytes_5))) ((app ((rev (bytes_6))) ((app ((rev (bytes_3))) ((app ((rev (bytes_4))) ((app ((rev (bytes))) ((rev (bytes_2)))))))))))) = (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))
.

Definition sm2_get_id_digest_entail_wit_22 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (u8_list_bounded (rev (bytes_2)) )) (PreH2 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH3 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_2)) = 32)) (PreH5 : (u8_list_bounded bytes_2 )) (PreH6 : (u8_list_bounded (rev (bytes)) )) (PreH7 : ((Zlength ((rev (bytes)))) = 32)) (PreH8 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes)) = 32)) (PreH10 : (u8_list_bounded bytes )) (PreH11 : (u8_list_bounded (rev (bytes_4)) )) (PreH12 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH13 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_4)) = 32)) (PreH15 : (u8_list_bounded bytes_4 )) (PreH16 : (u8_list_bounded (rev (bytes_3)) )) (PreH17 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH18 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_3)) = 32)) (PreH20 : (u8_list_bounded bytes_3 )) (PreH21 : (u8_list_bounded (rev (bytes_6)) )) (PreH22 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH23 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_6)) = 32)) (PreH25 : (u8_list_bounded bytes_6 )) (PreH26 : (u8_list_bounded (rev (bytes_5)) )) (PreH27 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH28 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_5)) = 32)) (PreH30 : (u8_list_bounded bytes_5 )) (PreH31 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH32 : ((Zlength (ID)) = id_len_pre)) (PreH33 : (u8_list_bounded ID )) (PreH34 : ((2 + id_len_pre ) <= 250)) (PreH35 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH36 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH37 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH38 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH40 : ((u8_list_value (bytes_4)) = y)) (PreH41 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH42 : ((u8_list_value (bytes_3)) = x)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_2)) = y_2)) (PreH45 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH46 : ((u8_list_value (bytes)) = x_2)) (PreH47 : (x_2 < SM2_P_Z)) (PreH48 : (0 <= x_2)) (PreH49 : (y_2 < SM2_P_Z)) (PreH50 : (0 <= y_2)) (PreH51 : (x < SM2_P_Z)) (PreH52 : (0 <= x)) (PreH53 : (y < SM2_P_Z)) (PreH54 : (0 <= y)) (PreH55 : (SM2_A_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_A_Z)) (PreH57 : (SM2_B_Z < SM2_P_Z)) (PreH58 : (0 <= SM2_B_Z)) (PreH59 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH60 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH61 : (y_2 = (sm2_point_y (P)))) (PreH62 : (x_2 = (sm2_point_x (P)))) (PreH63 : (afpoint_represents x_2 y_2 P )) (PreH64 : (afpoint_represents x y SM2_G_POINT )) (PreH65 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH66 : (id_len_pre <= 50)) (PreH67 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_23 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (u8_list_bounded (rev (bytes_2)) )) (PreH2 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH3 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_2)) = 32)) (PreH5 : (u8_list_bounded bytes_2 )) (PreH6 : (u8_list_bounded (rev (bytes)) )) (PreH7 : ((Zlength ((rev (bytes)))) = 32)) (PreH8 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes)) = 32)) (PreH10 : (u8_list_bounded bytes )) (PreH11 : (u8_list_bounded (rev (bytes_4)) )) (PreH12 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH13 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_4)) = 32)) (PreH15 : (u8_list_bounded bytes_4 )) (PreH16 : (u8_list_bounded (rev (bytes_3)) )) (PreH17 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH18 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_3)) = 32)) (PreH20 : (u8_list_bounded bytes_3 )) (PreH21 : (u8_list_bounded (rev (bytes_6)) )) (PreH22 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH23 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_6)) = 32)) (PreH25 : (u8_list_bounded bytes_6 )) (PreH26 : (u8_list_bounded (rev (bytes_5)) )) (PreH27 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH28 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_5)) = 32)) (PreH30 : (u8_list_bounded bytes_5 )) (PreH31 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH32 : ((Zlength (ID)) = id_len_pre)) (PreH33 : (u8_list_bounded ID )) (PreH34 : ((2 + id_len_pre ) <= 250)) (PreH35 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH36 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH37 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH38 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH40 : ((u8_list_value (bytes_4)) = y)) (PreH41 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH42 : ((u8_list_value (bytes_3)) = x)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_2)) = y_2)) (PreH45 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH46 : ((u8_list_value (bytes)) = x_2)) (PreH47 : (x_2 < SM2_P_Z)) (PreH48 : (0 <= x_2)) (PreH49 : (y_2 < SM2_P_Z)) (PreH50 : (0 <= y_2)) (PreH51 : (x < SM2_P_Z)) (PreH52 : (0 <= x)) (PreH53 : (y < SM2_P_Z)) (PreH54 : (0 <= y)) (PreH55 : (SM2_A_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_A_Z)) (PreH57 : (SM2_B_Z < SM2_P_Z)) (PreH58 : (0 <= SM2_B_Z)) (PreH59 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH60 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH61 : (y_2 = (sm2_point_y (P)))) (PreH62 : (x_2 = (sm2_point_x (P)))) (PreH63 : (afpoint_represents x_2 y_2 P )) (PreH64 : (afpoint_represents x y SM2_G_POINT )) (PreH65 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH66 : (id_len_pre <= 50)) (PreH67 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_24 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) (2 + id_len_pre ) ((2 + id_len_pre ) + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.seg ( &( "total" ) ) 0 ((2 + id_len_pre ) + 192 ) (app ((app ((sm2_entla_bytes (id_len_pre))) (ID))) ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_25 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 0 ((2 + id_len_pre ) + 192 ) (app ((app ((sm2_entla_bytes (id_len_pre))) (ID))) ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.full ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (app ((app ((sm2_entla_bytes (id_len_pre))) (ID))) ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_entail_wit_26 := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.full ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (app ((app ((sm2_entla_bytes (id_len_pre))) (ID))) ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  TT && emp 
|--
  “ ((Zlength ((sm2_za_input (ID) (P)))) = ((2 + id_len_pre ) + 192 )) ” 
  &&  “ (u8_list_bounded (sm2_za_input (ID) (P)) ) ” 
  &&  “ ((app ((app ((sm2_entla_bytes (id_len_pre))) (ID))) ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = (sm2_za_input (ID) (P))) ”
  &&  emp
).

Definition sm2_get_id_digest_entail_wit_26_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((Zlength ((sm2_za_input (ID) (P)))) = ((2 + id_len_pre ) + 192 ))
.

Definition sm2_get_id_digest_entail_wit_26_split_goal_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (u8_list_bounded (sm2_za_input (ID) (P)) )
.

Definition sm2_get_id_digest_entail_wit_26_split_goal_3 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((app ((app ((sm2_entla_bytes (id_len_pre))) (ID))) ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = (sm2_za_input (ID) (P)))
.

Definition sm2_get_id_digest_entail_wit_27 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((sm2_za_input (ID) (P)))) )
  **  (store_sm3_ti )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (retval_9 = 32) ” 
  &&  “ (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "charlist" ) ) (0 + 192 ) )
  **  (store_bytes (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((sm2_za_input (ID) (P)))) )
  **  (store_sm3_ti )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
.

Definition sm2_get_id_digest_entail_wit_28 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.undef_full ( &( "charlist" ) ) (0 + 192 ) )
  **  (store_bytes (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((sm2_za_input (ID) (P)))) )
  **  (store_sm3_ti )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
|--
  “ (retval_9 = 32) ” 
  &&  “ (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  (UCharArray.undef_full ( &( "charlist" ) ) (0 + 192 ) )
  **  (store_bytes result_pre 32 (sm3_digest_bytes ((sm2_za_input (ID) (P)))) )
  **  (store_sm3_ti )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
.

Definition sm2_get_id_digest_return_wit_1 := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes result_pre 32 (sm3_digest_bytes ((sm2_za_input (ID) (P)))) )
  **  (store_sm3_ti )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
|--
  “ (id_len_pre <= 50) ” 
  &&  “ (0 = 0) ”
  &&  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (store_sm2_za result_pre ID P (sm2_za_digest (ID) (P)) )
  **  (store_sm2_za_globals )
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_sm3_ti )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
|--
  “ ((sm3_digest_bytes ((sm2_za_input (ID) (P)))) = (sm2_za_digest (ID) (P))) ”
  &&  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
).

Definition sm2_get_id_digest_return_wit_1_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_sm3_ti )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
|--
  “ ((sm3_digest_bytes ((sm2_za_input (ID) (P)))) = (sm2_za_digest (ID) (P))) ”
.

Definition sm2_get_id_digest_return_wit_1_split_goal_spatial := 
forall (pubkey_pre: Z) (id_len_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (retval_9: Z) (PreH1 : (retval_9 = 32)) (PreH2 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH3 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH4 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH5 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH6 : (u8_list_bounded (rev (bytes_2)) )) (PreH7 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH8 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_2)) = 32)) (PreH10 : (u8_list_bounded bytes_2 )) (PreH11 : (u8_list_bounded (rev (bytes)) )) (PreH12 : ((Zlength ((rev (bytes)))) = 32)) (PreH13 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes)) = 32)) (PreH15 : (u8_list_bounded bytes )) (PreH16 : (u8_list_bounded (rev (bytes_4)) )) (PreH17 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH18 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_4)) = 32)) (PreH20 : (u8_list_bounded bytes_4 )) (PreH21 : (u8_list_bounded (rev (bytes_3)) )) (PreH22 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH23 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_3)) = 32)) (PreH25 : (u8_list_bounded bytes_3 )) (PreH26 : (u8_list_bounded (rev (bytes_6)) )) (PreH27 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH28 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH29 : ((Zlength (bytes_6)) = 32)) (PreH30 : (u8_list_bounded bytes_6 )) (PreH31 : (u8_list_bounded (rev (bytes_5)) )) (PreH32 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH33 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH34 : ((Zlength (bytes_5)) = 32)) (PreH35 : (u8_list_bounded bytes_5 )) (PreH36 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH37 : ((Zlength (ID)) = id_len_pre)) (PreH38 : (u8_list_bounded ID )) (PreH39 : ((2 + id_len_pre ) <= 250)) (PreH40 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH41 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH42 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH43 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_4)) = y)) (PreH46 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH47 : ((u8_list_value (bytes_3)) = x)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH49 : ((u8_list_value (bytes_2)) = y_2)) (PreH50 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH51 : ((u8_list_value (bytes)) = x_2)) (PreH52 : (x_2 < SM2_P_Z)) (PreH53 : (0 <= x_2)) (PreH54 : (y_2 < SM2_P_Z)) (PreH55 : (0 <= y_2)) (PreH56 : (x < SM2_P_Z)) (PreH57 : (0 <= x)) (PreH58 : (y < SM2_P_Z)) (PreH59 : (0 <= y)) (PreH60 : (SM2_A_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_A_Z)) (PreH62 : (SM2_B_Z < SM2_P_Z)) (PreH63 : (0 <= SM2_B_Z)) (PreH64 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH65 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH66 : (y_2 = (sm2_point_y (P)))) (PreH67 : (x_2 = (sm2_point_x (P)))) (PreH68 : (afpoint_represents x_2 y_2 P )) (PreH69 : (afpoint_represents x y SM2_G_POINT )) (PreH70 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH71 : (id_len_pre <= 50)) (PreH72 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_sm3_ti )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
|--
  (store_sm3_ti )
  **  (store_sm2_b )
  **  (store_sm2_a )
.

Definition sm2_get_id_digest_return_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (id_len_pre > 50)) (PreH2 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (id_len_pre > 50) ” 
  &&  “ ((-1) = (-1)) ”
  &&  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
.

Definition sm2_get_id_digest_partial_solve_wit_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (PreH1 : (id_len_pre <= 50)) (PreH2 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
|--
  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full ( &( "total" ) ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_afpoint pubkey_pre P )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm2_za_globals )
.

Definition sm2_get_id_digest_partial_solve_wit_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (((( &( "total" ) ) + (0 * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.mixed_missing_i ( &( "total" ) ) 0 0 250 (repeat_Z (None) (250)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_3 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH2 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH3 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH4 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH5 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH6 : ((u8_list_value (bytes_4)) = y)) (PreH7 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH8 : ((u8_list_value (bytes_3)) = x)) (PreH9 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_2)) = y_2)) (PreH11 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH12 : ((u8_list_value (bytes)) = x_2)) (PreH13 : (x_2 < SM2_P_Z)) (PreH14 : (0 <= x_2)) (PreH15 : (y_2 < SM2_P_Z)) (PreH16 : (0 <= y_2)) (PreH17 : (x < SM2_P_Z)) (PreH18 : (0 <= x)) (PreH19 : (y < SM2_P_Z)) (PreH20 : (0 <= y)) (PreH21 : (SM2_A_Z < SM2_P_Z)) (PreH22 : (0 <= SM2_A_Z)) (PreH23 : (SM2_B_Z < SM2_P_Z)) (PreH24 : (0 <= SM2_B_Z)) (PreH25 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH26 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH27 : (y_2 = (sm2_point_y (P)))) (PreH28 : (x_2 = (sm2_point_x (P)))) (PreH29 : (afpoint_represents x_2 y_2 P )) (PreH30 : (afpoint_represents x y SM2_G_POINT )) (PreH31 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH32 : (id_len_pre <= 50)) (PreH33 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.mixed_full ( &( "total" ) ) 250 (replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (((( &( "total" ) ) + (1 * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.mixed_missing_i ( &( "total" ) ) 1 0 250 (replace_Znth (0) ((Some ((unsigned_last_nbits (((Z.shiftr (id_len_pre * 8 ) 8) % ( 256 ) )) (8))))) ((repeat_Z (None) (250)))) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_4_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : ((2 + id_len_pre ) <= 250)) (PreH2 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH3 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH4 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH5 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH6 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH7 : ((u8_list_value (bytes_4)) = y)) (PreH8 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH9 : ((u8_list_value (bytes_3)) = x)) (PreH10 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH11 : ((u8_list_value (bytes_2)) = y_2)) (PreH12 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH13 : ((u8_list_value (bytes)) = x_2)) (PreH14 : (x_2 < SM2_P_Z)) (PreH15 : (0 <= x_2)) (PreH16 : (y_2 < SM2_P_Z)) (PreH17 : (0 <= y_2)) (PreH18 : (x < SM2_P_Z)) (PreH19 : (0 <= x)) (PreH20 : (y < SM2_P_Z)) (PreH21 : (0 <= y)) (PreH22 : (SM2_A_Z < SM2_P_Z)) (PreH23 : (0 <= SM2_A_Z)) (PreH24 : (SM2_B_Z < SM2_P_Z)) (PreH25 : (0 <= SM2_B_Z)) (PreH26 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH27 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH28 : (y_2 = (sm2_point_y (P)))) (PreH29 : (x_2 = (sm2_point_x (P)))) (PreH30 : (afpoint_represents x_2 y_2 P )) (PreH31 : (afpoint_represents x y SM2_G_POINT )) (PreH32 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH33 : (id_len_pre <= 50)) (PreH34 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "total" ) ) + (2 * sizeof(UCHAR))) = (( &( "total" ) ) + (2 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (0 <= id_len_pre) ”
.

Definition sm2_get_id_digest_partial_solve_wit_4_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (PreH1 : ((2 + id_len_pre ) <= 250)) (PreH2 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH3 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH4 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH5 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH6 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH7 : ((u8_list_value (bytes_4)) = y)) (PreH8 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH9 : ((u8_list_value (bytes_3)) = x)) (PreH10 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH11 : ((u8_list_value (bytes_2)) = y_2)) (PreH12 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH13 : ((u8_list_value (bytes)) = x_2)) (PreH14 : (x_2 < SM2_P_Z)) (PreH15 : (0 <= x_2)) (PreH16 : (y_2 < SM2_P_Z)) (PreH17 : (0 <= y_2)) (PreH18 : (x < SM2_P_Z)) (PreH19 : (0 <= x)) (PreH20 : (y < SM2_P_Z)) (PreH21 : (0 <= y)) (PreH22 : (SM2_A_Z < SM2_P_Z)) (PreH23 : (0 <= SM2_A_Z)) (PreH24 : (SM2_B_Z < SM2_P_Z)) (PreH25 : (0 <= SM2_B_Z)) (PreH26 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH27 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH28 : (y_2 = (sm2_point_y (P)))) (PreH29 : (x_2 = (sm2_point_x (P)))) (PreH30 : (afpoint_represents x_2 y_2 P )) (PreH31 : (afpoint_represents x y SM2_G_POINT )) (PreH32 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH33 : (id_len_pre <= 50)) (PreH34 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "total" ) ) + (2 * sizeof(UCHAR))) = (( &( "total" ) ) + (2 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (0 <= id_len_pre) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "total" ) ) 2 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_4 := sm2_get_id_digest_partial_solve_wit_4_pure -> sm2_get_id_digest_partial_solve_wit_4_aux.

Definition sm2_get_id_digest_partial_solve_wit_5_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH2 : ((Zlength (ID)) = id_len_pre)) (PreH3 : (u8_list_bounded ID )) (PreH4 : ((2 + id_len_pre ) <= 250)) (PreH5 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH6 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH7 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH8 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH9 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_4)) = y)) (PreH11 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH12 : ((u8_list_value (bytes_3)) = x)) (PreH13 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH14 : ((u8_list_value (bytes_2)) = y_2)) (PreH15 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH16 : ((u8_list_value (bytes)) = x_2)) (PreH17 : (x_2 < SM2_P_Z)) (PreH18 : (0 <= x_2)) (PreH19 : (y_2 < SM2_P_Z)) (PreH20 : (0 <= y_2)) (PreH21 : (x < SM2_P_Z)) (PreH22 : (0 <= x)) (PreH23 : (y < SM2_P_Z)) (PreH24 : (0 <= y)) (PreH25 : (SM2_A_Z < SM2_P_Z)) (PreH26 : (0 <= SM2_A_Z)) (PreH27 : (SM2_B_Z < SM2_P_Z)) (PreH28 : (0 <= SM2_B_Z)) (PreH29 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH30 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH31 : (y_2 = (sm2_point_y (P)))) (PreH32 : (x_2 = (sm2_point_x (P)))) (PreH33 : (afpoint_represents x_2 y_2 P )) (PreH34 : (afpoint_represents x y SM2_G_POINT )) (PreH35 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH36 : (id_len_pre <= 50)) (PreH37 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (0 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 32 ) <= 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_5_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (PreH1 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH2 : ((Zlength (ID)) = id_len_pre)) (PreH3 : (u8_list_bounded ID )) (PreH4 : ((2 + id_len_pre ) <= 250)) (PreH5 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH6 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH7 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH8 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH9 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH10 : ((u8_list_value (bytes_4)) = y)) (PreH11 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH12 : ((u8_list_value (bytes_3)) = x)) (PreH13 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH14 : ((u8_list_value (bytes_2)) = y_2)) (PreH15 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH16 : ((u8_list_value (bytes)) = x_2)) (PreH17 : (x_2 < SM2_P_Z)) (PreH18 : (0 <= x_2)) (PreH19 : (y_2 < SM2_P_Z)) (PreH20 : (0 <= y_2)) (PreH21 : (x < SM2_P_Z)) (PreH22 : (0 <= x)) (PreH23 : (y < SM2_P_Z)) (PreH24 : (0 <= y)) (PreH25 : (SM2_A_Z < SM2_P_Z)) (PreH26 : (0 <= SM2_A_Z)) (PreH27 : (SM2_B_Z < SM2_P_Z)) (PreH28 : (0 <= SM2_B_Z)) (PreH29 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH30 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH31 : (y_2 = (sm2_point_y (P)))) (PreH32 : (x_2 = (sm2_point_x (P)))) (PreH33 : (afpoint_represents x_2 y_2 P )) (PreH34 : (afpoint_represents x y SM2_G_POINT )) (PreH35 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH36 : (id_len_pre <= 50)) (PreH37 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full ( &( "charlist" ) ) 192 )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (0 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + 32 ) <= 192) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "charlist" ) ) 0 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_5 := sm2_get_id_digest_partial_solve_wit_5_pure -> sm2_get_id_digest_partial_solve_wit_5_aux.

Definition sm2_get_id_digest_partial_solve_wit_6_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_5)) = 32)) (PreH3 : (u8_list_bounded bytes_5 )) (PreH4 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH5 : ((Zlength (ID)) = id_len_pre)) (PreH6 : (u8_list_bounded ID )) (PreH7 : ((2 + id_len_pre ) <= 250)) (PreH8 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH9 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH10 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH11 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH12 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH13 : ((u8_list_value (bytes_4)) = y)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH15 : ((u8_list_value (bytes_3)) = x)) (PreH16 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH17 : ((u8_list_value (bytes_2)) = y_2)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH19 : ((u8_list_value (bytes)) = x_2)) (PreH20 : (x_2 < SM2_P_Z)) (PreH21 : (0 <= x_2)) (PreH22 : (y_2 < SM2_P_Z)) (PreH23 : (0 <= y_2)) (PreH24 : (x < SM2_P_Z)) (PreH25 : (0 <= x)) (PreH26 : (y < SM2_P_Z)) (PreH27 : (0 <= y)) (PreH28 : (SM2_A_Z < SM2_P_Z)) (PreH29 : (0 <= SM2_A_Z)) (PreH30 : (SM2_B_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_B_Z)) (PreH32 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH33 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH34 : (y_2 = (sm2_point_y (P)))) (PreH35 : (x_2 = (sm2_point_x (P)))) (PreH36 : (afpoint_represents x_2 y_2 P )) (PreH37 : (afpoint_represents x y SM2_G_POINT )) (PreH38 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH39 : (id_len_pre <= 50)) (PreH40 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) bytes_5 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ”
.

Definition sm2_get_id_digest_partial_solve_wit_6_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_5)) = 32)) (PreH3 : (u8_list_bounded bytes_5 )) (PreH4 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH5 : ((Zlength (ID)) = id_len_pre)) (PreH6 : (u8_list_bounded ID )) (PreH7 : ((2 + id_len_pre ) <= 250)) (PreH8 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH9 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH10 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH11 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH12 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH13 : ((u8_list_value (bytes_4)) = y)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH15 : ((u8_list_value (bytes_3)) = x)) (PreH16 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH17 : ((u8_list_value (bytes_2)) = y_2)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH19 : ((u8_list_value (bytes)) = x_2)) (PreH20 : (x_2 < SM2_P_Z)) (PreH21 : (0 <= x_2)) (PreH22 : (y_2 < SM2_P_Z)) (PreH23 : (0 <= y_2)) (PreH24 : (x < SM2_P_Z)) (PreH25 : (0 <= x)) (PreH26 : (y < SM2_P_Z)) (PreH27 : (0 <= y)) (PreH28 : (SM2_A_Z < SM2_P_Z)) (PreH29 : (0 <= SM2_A_Z)) (PreH30 : (SM2_B_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_B_Z)) (PreH32 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH33 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH34 : (y_2 = (sm2_point_y (P)))) (PreH35 : (x_2 = (sm2_point_x (P)))) (PreH36 : (afpoint_represents x_2 y_2 P )) (PreH37 : (afpoint_represents x y SM2_G_POINT )) (PreH38 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH39 : (id_len_pre <= 50)) (PreH40 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) bytes_5 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "charlist" ) ) + (0 * sizeof(UCHAR))) 32 bytes_5 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_6 := sm2_get_id_digest_partial_solve_wit_6_pure -> sm2_get_id_digest_partial_solve_wit_6_aux.

Definition sm2_get_id_digest_partial_solve_wit_7_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (u8_list_bounded (rev (bytes_5)) )) (PreH2 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH3 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_5)) = 32)) (PreH5 : (u8_list_bounded bytes_5 )) (PreH6 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH7 : ((Zlength (ID)) = id_len_pre)) (PreH8 : (u8_list_bounded ID )) (PreH9 : ((2 + id_len_pre ) <= 250)) (PreH10 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH11 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH12 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH13 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH15 : ((u8_list_value (bytes_4)) = y)) (PreH16 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH17 : ((u8_list_value (bytes_3)) = x)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH19 : ((u8_list_value (bytes_2)) = y_2)) (PreH20 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH21 : ((u8_list_value (bytes)) = x_2)) (PreH22 : (x_2 < SM2_P_Z)) (PreH23 : (0 <= x_2)) (PreH24 : (y_2 < SM2_P_Z)) (PreH25 : (0 <= y_2)) (PreH26 : (x < SM2_P_Z)) (PreH27 : (0 <= x)) (PreH28 : (y < SM2_P_Z)) (PreH29 : (0 <= y)) (PreH30 : (SM2_A_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_A_Z)) (PreH32 : (SM2_B_Z < SM2_P_Z)) (PreH33 : (0 <= SM2_B_Z)) (PreH34 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH35 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH36 : (y_2 = (sm2_point_y (P)))) (PreH37 : (x_2 = (sm2_point_x (P)))) (PreH38 : (afpoint_represents x_2 y_2 P )) (PreH39 : (afpoint_represents x y SM2_G_POINT )) (PreH40 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH41 : (id_len_pre <= 50)) (PreH42 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (32 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (32 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 32) ” 
  &&  “ ((32 + 32 ) <= 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_7_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (u8_list_bounded (rev (bytes_5)) )) (PreH2 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH3 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_5)) = 32)) (PreH5 : (u8_list_bounded bytes_5 )) (PreH6 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH7 : ((Zlength (ID)) = id_len_pre)) (PreH8 : (u8_list_bounded ID )) (PreH9 : ((2 + id_len_pre ) <= 250)) (PreH10 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH11 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH12 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH13 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH14 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH15 : ((u8_list_value (bytes_4)) = y)) (PreH16 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH17 : ((u8_list_value (bytes_3)) = x)) (PreH18 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH19 : ((u8_list_value (bytes_2)) = y_2)) (PreH20 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH21 : ((u8_list_value (bytes)) = x_2)) (PreH22 : (x_2 < SM2_P_Z)) (PreH23 : (0 <= x_2)) (PreH24 : (y_2 < SM2_P_Z)) (PreH25 : (0 <= y_2)) (PreH26 : (x < SM2_P_Z)) (PreH27 : (0 <= x)) (PreH28 : (y < SM2_P_Z)) (PreH29 : (0 <= y)) (PreH30 : (SM2_A_Z < SM2_P_Z)) (PreH31 : (0 <= SM2_A_Z)) (PreH32 : (SM2_B_Z < SM2_P_Z)) (PreH33 : (0 <= SM2_B_Z)) (PreH34 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH35 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH36 : (y_2 = (sm2_point_y (P)))) (PreH37 : (x_2 = (sm2_point_x (P)))) (PreH38 : (afpoint_represents x_2 y_2 P )) (PreH39 : (afpoint_represents x y SM2_G_POINT )) (PreH40 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH41 : (id_len_pre <= 50)) (PreH42 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (0 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (32 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (32 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 32) ” 
  &&  “ ((32 + 32 ) <= 192) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "charlist" ) ) 32 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_7 := sm2_get_id_digest_partial_solve_wit_7_pure -> sm2_get_id_digest_partial_solve_wit_7_aux.

Definition sm2_get_id_digest_partial_solve_wit_8_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_6)) = 32)) (PreH3 : (u8_list_bounded bytes_6 )) (PreH4 : (u8_list_bounded (rev (bytes_5)) )) (PreH5 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH6 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_5)) = 32)) (PreH8 : (u8_list_bounded bytes_5 )) (PreH9 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH10 : ((Zlength (ID)) = id_len_pre)) (PreH11 : (u8_list_bounded ID )) (PreH12 : ((2 + id_len_pre ) <= 250)) (PreH13 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH14 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH15 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH16 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH17 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH18 : ((u8_list_value (bytes_4)) = y)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH20 : ((u8_list_value (bytes_3)) = x)) (PreH21 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH22 : ((u8_list_value (bytes_2)) = y_2)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH24 : ((u8_list_value (bytes)) = x_2)) (PreH25 : (x_2 < SM2_P_Z)) (PreH26 : (0 <= x_2)) (PreH27 : (y_2 < SM2_P_Z)) (PreH28 : (0 <= y_2)) (PreH29 : (x < SM2_P_Z)) (PreH30 : (0 <= x)) (PreH31 : (y < SM2_P_Z)) (PreH32 : (0 <= y)) (PreH33 : (SM2_A_Z < SM2_P_Z)) (PreH34 : (0 <= SM2_A_Z)) (PreH35 : (SM2_B_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_B_Z)) (PreH37 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH38 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH39 : (y_2 = (sm2_point_y (P)))) (PreH40 : (x_2 = (sm2_point_x (P)))) (PreH41 : (afpoint_represents x_2 y_2 P )) (PreH42 : (afpoint_represents x y SM2_G_POINT )) (PreH43 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH44 : (id_len_pre <= 50)) (PreH45 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) bytes_6 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ”
.

Definition sm2_get_id_digest_partial_solve_wit_8_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_6)) = 32)) (PreH3 : (u8_list_bounded bytes_6 )) (PreH4 : (u8_list_bounded (rev (bytes_5)) )) (PreH5 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH6 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_5)) = 32)) (PreH8 : (u8_list_bounded bytes_5 )) (PreH9 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH10 : ((Zlength (ID)) = id_len_pre)) (PreH11 : (u8_list_bounded ID )) (PreH12 : ((2 + id_len_pre ) <= 250)) (PreH13 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH14 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH15 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH16 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH17 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH18 : ((u8_list_value (bytes_4)) = y)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH20 : ((u8_list_value (bytes_3)) = x)) (PreH21 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH22 : ((u8_list_value (bytes_2)) = y_2)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH24 : ((u8_list_value (bytes)) = x_2)) (PreH25 : (x_2 < SM2_P_Z)) (PreH26 : (0 <= x_2)) (PreH27 : (y_2 < SM2_P_Z)) (PreH28 : (0 <= y_2)) (PreH29 : (x < SM2_P_Z)) (PreH30 : (0 <= x)) (PreH31 : (y < SM2_P_Z)) (PreH32 : (0 <= y)) (PreH33 : (SM2_A_Z < SM2_P_Z)) (PreH34 : (0 <= SM2_A_Z)) (PreH35 : (SM2_B_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_B_Z)) (PreH37 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH38 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH39 : (y_2 = (sm2_point_y (P)))) (PreH40 : (x_2 = (sm2_point_x (P)))) (PreH41 : (afpoint_represents x_2 y_2 P )) (PreH42 : (afpoint_represents x y SM2_G_POINT )) (PreH43 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH44 : (id_len_pre <= 50)) (PreH45 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) bytes_6 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "charlist" ) ) + (32 * sizeof(UCHAR))) 32 bytes_6 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_8 := sm2_get_id_digest_partial_solve_wit_8_pure -> sm2_get_id_digest_partial_solve_wit_8_aux.

Definition sm2_get_id_digest_partial_solve_wit_9_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (u8_list_bounded (rev (bytes_6)) )) (PreH2 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH3 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_6)) = 32)) (PreH5 : (u8_list_bounded bytes_6 )) (PreH6 : (u8_list_bounded (rev (bytes_5)) )) (PreH7 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH8 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_5)) = 32)) (PreH10 : (u8_list_bounded bytes_5 )) (PreH11 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH12 : ((Zlength (ID)) = id_len_pre)) (PreH13 : (u8_list_bounded ID )) (PreH14 : ((2 + id_len_pre ) <= 250)) (PreH15 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH16 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH17 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH18 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH20 : ((u8_list_value (bytes_4)) = y)) (PreH21 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH22 : ((u8_list_value (bytes_3)) = x)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH24 : ((u8_list_value (bytes_2)) = y_2)) (PreH25 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH26 : ((u8_list_value (bytes)) = x_2)) (PreH27 : (x_2 < SM2_P_Z)) (PreH28 : (0 <= x_2)) (PreH29 : (y_2 < SM2_P_Z)) (PreH30 : (0 <= y_2)) (PreH31 : (x < SM2_P_Z)) (PreH32 : (0 <= x)) (PreH33 : (y < SM2_P_Z)) (PreH34 : (0 <= y)) (PreH35 : (SM2_A_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_A_Z)) (PreH37 : (SM2_B_Z < SM2_P_Z)) (PreH38 : (0 <= SM2_B_Z)) (PreH39 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH40 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH41 : (y_2 = (sm2_point_y (P)))) (PreH42 : (x_2 = (sm2_point_x (P)))) (PreH43 : (afpoint_represents x_2 y_2 P )) (PreH44 : (afpoint_represents x y SM2_G_POINT )) (PreH45 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH46 : (id_len_pre <= 50)) (PreH47 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (64 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (64 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 64) ” 
  &&  “ ((64 + 32 ) <= 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_9_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (u8_list_bounded (rev (bytes_6)) )) (PreH2 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH3 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_6)) = 32)) (PreH5 : (u8_list_bounded bytes_6 )) (PreH6 : (u8_list_bounded (rev (bytes_5)) )) (PreH7 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH8 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_5)) = 32)) (PreH10 : (u8_list_bounded bytes_5 )) (PreH11 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH12 : ((Zlength (ID)) = id_len_pre)) (PreH13 : (u8_list_bounded ID )) (PreH14 : ((2 + id_len_pre ) <= 250)) (PreH15 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH16 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH17 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH18 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH19 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH20 : ((u8_list_value (bytes_4)) = y)) (PreH21 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH22 : ((u8_list_value (bytes_3)) = x)) (PreH23 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH24 : ((u8_list_value (bytes_2)) = y_2)) (PreH25 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH26 : ((u8_list_value (bytes)) = x_2)) (PreH27 : (x_2 < SM2_P_Z)) (PreH28 : (0 <= x_2)) (PreH29 : (y_2 < SM2_P_Z)) (PreH30 : (0 <= y_2)) (PreH31 : (x < SM2_P_Z)) (PreH32 : (0 <= x)) (PreH33 : (y < SM2_P_Z)) (PreH34 : (0 <= y)) (PreH35 : (SM2_A_Z < SM2_P_Z)) (PreH36 : (0 <= SM2_A_Z)) (PreH37 : (SM2_B_Z < SM2_P_Z)) (PreH38 : (0 <= SM2_B_Z)) (PreH39 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH40 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH41 : (y_2 = (sm2_point_y (P)))) (PreH42 : (x_2 = (sm2_point_x (P)))) (PreH43 : (afpoint_represents x_2 y_2 P )) (PreH44 : (afpoint_represents x y SM2_G_POINT )) (PreH45 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH46 : (id_len_pre <= 50)) (PreH47 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (32 + 32 ) 192 )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (64 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (64 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 64) ” 
  &&  “ ((64 + 32 ) <= 192) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "charlist" ) ) 64 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_9 := sm2_get_id_digest_partial_solve_wit_9_pure -> sm2_get_id_digest_partial_solve_wit_9_aux.

Definition sm2_get_id_digest_partial_solve_wit_10_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_3)) = 32)) (PreH3 : (u8_list_bounded bytes_3 )) (PreH4 : (u8_list_bounded (rev (bytes_6)) )) (PreH5 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH6 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_6)) = 32)) (PreH8 : (u8_list_bounded bytes_6 )) (PreH9 : (u8_list_bounded (rev (bytes_5)) )) (PreH10 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH11 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_5)) = 32)) (PreH13 : (u8_list_bounded bytes_5 )) (PreH14 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH15 : ((Zlength (ID)) = id_len_pre)) (PreH16 : (u8_list_bounded ID )) (PreH17 : ((2 + id_len_pre ) <= 250)) (PreH18 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH19 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH20 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH21 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH22 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH23 : ((u8_list_value (bytes_4)) = y)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH25 : ((u8_list_value (bytes_3)) = x)) (PreH26 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH27 : ((u8_list_value (bytes_2)) = y_2)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH29 : ((u8_list_value (bytes)) = x_2)) (PreH30 : (x_2 < SM2_P_Z)) (PreH31 : (0 <= x_2)) (PreH32 : (y_2 < SM2_P_Z)) (PreH33 : (0 <= y_2)) (PreH34 : (x < SM2_P_Z)) (PreH35 : (0 <= x)) (PreH36 : (y < SM2_P_Z)) (PreH37 : (0 <= y)) (PreH38 : (SM2_A_Z < SM2_P_Z)) (PreH39 : (0 <= SM2_A_Z)) (PreH40 : (SM2_B_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_B_Z)) (PreH42 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH43 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH44 : (y_2 = (sm2_point_y (P)))) (PreH45 : (x_2 = (sm2_point_x (P)))) (PreH46 : (afpoint_represents x_2 y_2 P )) (PreH47 : (afpoint_represents x y SM2_G_POINT )) (PreH48 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH49 : (id_len_pre <= 50)) (PreH50 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) bytes_3 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ”
.

Definition sm2_get_id_digest_partial_solve_wit_10_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_3)) = 32)) (PreH3 : (u8_list_bounded bytes_3 )) (PreH4 : (u8_list_bounded (rev (bytes_6)) )) (PreH5 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH6 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_6)) = 32)) (PreH8 : (u8_list_bounded bytes_6 )) (PreH9 : (u8_list_bounded (rev (bytes_5)) )) (PreH10 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH11 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_5)) = 32)) (PreH13 : (u8_list_bounded bytes_5 )) (PreH14 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH15 : ((Zlength (ID)) = id_len_pre)) (PreH16 : (u8_list_bounded ID )) (PreH17 : ((2 + id_len_pre ) <= 250)) (PreH18 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH19 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH20 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH21 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH22 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH23 : ((u8_list_value (bytes_4)) = y)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH25 : ((u8_list_value (bytes_3)) = x)) (PreH26 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH27 : ((u8_list_value (bytes_2)) = y_2)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH29 : ((u8_list_value (bytes)) = x_2)) (PreH30 : (x_2 < SM2_P_Z)) (PreH31 : (0 <= x_2)) (PreH32 : (y_2 < SM2_P_Z)) (PreH33 : (0 <= y_2)) (PreH34 : (x < SM2_P_Z)) (PreH35 : (0 <= x)) (PreH36 : (y < SM2_P_Z)) (PreH37 : (0 <= y)) (PreH38 : (SM2_A_Z < SM2_P_Z)) (PreH39 : (0 <= SM2_A_Z)) (PreH40 : (SM2_B_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_B_Z)) (PreH42 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH43 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH44 : (y_2 = (sm2_point_y (P)))) (PreH45 : (x_2 = (sm2_point_x (P)))) (PreH46 : (afpoint_represents x_2 y_2 P )) (PreH47 : (afpoint_represents x y SM2_G_POINT )) (PreH48 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH49 : (id_len_pre <= 50)) (PreH50 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) bytes_3 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "charlist" ) ) + (64 * sizeof(UCHAR))) 32 bytes_3 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_10 := sm2_get_id_digest_partial_solve_wit_10_pure -> sm2_get_id_digest_partial_solve_wit_10_aux.

Definition sm2_get_id_digest_partial_solve_wit_11_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (u8_list_bounded (rev (bytes_3)) )) (PreH2 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH3 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_3)) = 32)) (PreH5 : (u8_list_bounded bytes_3 )) (PreH6 : (u8_list_bounded (rev (bytes_6)) )) (PreH7 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH8 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_6)) = 32)) (PreH10 : (u8_list_bounded bytes_6 )) (PreH11 : (u8_list_bounded (rev (bytes_5)) )) (PreH12 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH13 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_5)) = 32)) (PreH15 : (u8_list_bounded bytes_5 )) (PreH16 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH17 : ((Zlength (ID)) = id_len_pre)) (PreH18 : (u8_list_bounded ID )) (PreH19 : ((2 + id_len_pre ) <= 250)) (PreH20 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH21 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH22 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH23 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH25 : ((u8_list_value (bytes_4)) = y)) (PreH26 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH27 : ((u8_list_value (bytes_3)) = x)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH29 : ((u8_list_value (bytes_2)) = y_2)) (PreH30 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH31 : ((u8_list_value (bytes)) = x_2)) (PreH32 : (x_2 < SM2_P_Z)) (PreH33 : (0 <= x_2)) (PreH34 : (y_2 < SM2_P_Z)) (PreH35 : (0 <= y_2)) (PreH36 : (x < SM2_P_Z)) (PreH37 : (0 <= x)) (PreH38 : (y < SM2_P_Z)) (PreH39 : (0 <= y)) (PreH40 : (SM2_A_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_A_Z)) (PreH42 : (SM2_B_Z < SM2_P_Z)) (PreH43 : (0 <= SM2_B_Z)) (PreH44 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH45 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH46 : (y_2 = (sm2_point_y (P)))) (PreH47 : (x_2 = (sm2_point_x (P)))) (PreH48 : (afpoint_represents x_2 y_2 P )) (PreH49 : (afpoint_represents x y SM2_G_POINT )) (PreH50 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH51 : (id_len_pre <= 50)) (PreH52 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (96 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (96 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 96) ” 
  &&  “ ((96 + 32 ) <= 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_11_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (u8_list_bounded (rev (bytes_3)) )) (PreH2 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH3 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_3)) = 32)) (PreH5 : (u8_list_bounded bytes_3 )) (PreH6 : (u8_list_bounded (rev (bytes_6)) )) (PreH7 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH8 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_6)) = 32)) (PreH10 : (u8_list_bounded bytes_6 )) (PreH11 : (u8_list_bounded (rev (bytes_5)) )) (PreH12 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH13 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_5)) = 32)) (PreH15 : (u8_list_bounded bytes_5 )) (PreH16 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH17 : ((Zlength (ID)) = id_len_pre)) (PreH18 : (u8_list_bounded ID )) (PreH19 : ((2 + id_len_pre ) <= 250)) (PreH20 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH21 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH22 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH23 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH24 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH25 : ((u8_list_value (bytes_4)) = y)) (PreH26 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH27 : ((u8_list_value (bytes_3)) = x)) (PreH28 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH29 : ((u8_list_value (bytes_2)) = y_2)) (PreH30 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH31 : ((u8_list_value (bytes)) = x_2)) (PreH32 : (x_2 < SM2_P_Z)) (PreH33 : (0 <= x_2)) (PreH34 : (y_2 < SM2_P_Z)) (PreH35 : (0 <= y_2)) (PreH36 : (x < SM2_P_Z)) (PreH37 : (0 <= x)) (PreH38 : (y < SM2_P_Z)) (PreH39 : (0 <= y)) (PreH40 : (SM2_A_Z < SM2_P_Z)) (PreH41 : (0 <= SM2_A_Z)) (PreH42 : (SM2_B_Z < SM2_P_Z)) (PreH43 : (0 <= SM2_B_Z)) (PreH44 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH45 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH46 : (y_2 = (sm2_point_y (P)))) (PreH47 : (x_2 = (sm2_point_x (P)))) (PreH48 : (afpoint_represents x_2 y_2 P )) (PreH49 : (afpoint_represents x y SM2_G_POINT )) (PreH50 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH51 : (id_len_pre <= 50)) (PreH52 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (64 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (96 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (96 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 96) ” 
  &&  “ ((96 + 32 ) <= 192) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "charlist" ) ) 96 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_11 := sm2_get_id_digest_partial_solve_wit_11_pure -> sm2_get_id_digest_partial_solve_wit_11_aux.

Definition sm2_get_id_digest_partial_solve_wit_12_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_4)) = 32)) (PreH3 : (u8_list_bounded bytes_4 )) (PreH4 : (u8_list_bounded (rev (bytes_3)) )) (PreH5 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH6 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_3)) = 32)) (PreH8 : (u8_list_bounded bytes_3 )) (PreH9 : (u8_list_bounded (rev (bytes_6)) )) (PreH10 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH11 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_6)) = 32)) (PreH13 : (u8_list_bounded bytes_6 )) (PreH14 : (u8_list_bounded (rev (bytes_5)) )) (PreH15 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH16 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_5)) = 32)) (PreH18 : (u8_list_bounded bytes_5 )) (PreH19 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH20 : ((Zlength (ID)) = id_len_pre)) (PreH21 : (u8_list_bounded ID )) (PreH22 : ((2 + id_len_pre ) <= 250)) (PreH23 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH24 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH25 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH26 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH27 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH28 : ((u8_list_value (bytes_4)) = y)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH30 : ((u8_list_value (bytes_3)) = x)) (PreH31 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH32 : ((u8_list_value (bytes_2)) = y_2)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH34 : ((u8_list_value (bytes)) = x_2)) (PreH35 : (x_2 < SM2_P_Z)) (PreH36 : (0 <= x_2)) (PreH37 : (y_2 < SM2_P_Z)) (PreH38 : (0 <= y_2)) (PreH39 : (x < SM2_P_Z)) (PreH40 : (0 <= x)) (PreH41 : (y < SM2_P_Z)) (PreH42 : (0 <= y)) (PreH43 : (SM2_A_Z < SM2_P_Z)) (PreH44 : (0 <= SM2_A_Z)) (PreH45 : (SM2_B_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_B_Z)) (PreH47 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH48 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH49 : (y_2 = (sm2_point_y (P)))) (PreH50 : (x_2 = (sm2_point_x (P)))) (PreH51 : (afpoint_represents x_2 y_2 P )) (PreH52 : (afpoint_represents x y SM2_G_POINT )) (PreH53 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH54 : (id_len_pre <= 50)) (PreH55 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) bytes_4 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ”
.

Definition sm2_get_id_digest_partial_solve_wit_12_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_4)) = 32)) (PreH3 : (u8_list_bounded bytes_4 )) (PreH4 : (u8_list_bounded (rev (bytes_3)) )) (PreH5 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH6 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_3)) = 32)) (PreH8 : (u8_list_bounded bytes_3 )) (PreH9 : (u8_list_bounded (rev (bytes_6)) )) (PreH10 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH11 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_6)) = 32)) (PreH13 : (u8_list_bounded bytes_6 )) (PreH14 : (u8_list_bounded (rev (bytes_5)) )) (PreH15 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH16 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_5)) = 32)) (PreH18 : (u8_list_bounded bytes_5 )) (PreH19 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH20 : ((Zlength (ID)) = id_len_pre)) (PreH21 : (u8_list_bounded ID )) (PreH22 : ((2 + id_len_pre ) <= 250)) (PreH23 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH24 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH25 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH26 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH27 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH28 : ((u8_list_value (bytes_4)) = y)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH30 : ((u8_list_value (bytes_3)) = x)) (PreH31 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH32 : ((u8_list_value (bytes_2)) = y_2)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH34 : ((u8_list_value (bytes)) = x_2)) (PreH35 : (x_2 < SM2_P_Z)) (PreH36 : (0 <= x_2)) (PreH37 : (y_2 < SM2_P_Z)) (PreH38 : (0 <= y_2)) (PreH39 : (x < SM2_P_Z)) (PreH40 : (0 <= x)) (PreH41 : (y < SM2_P_Z)) (PreH42 : (0 <= y)) (PreH43 : (SM2_A_Z < SM2_P_Z)) (PreH44 : (0 <= SM2_A_Z)) (PreH45 : (SM2_B_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_B_Z)) (PreH47 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH48 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH49 : (y_2 = (sm2_point_y (P)))) (PreH50 : (x_2 = (sm2_point_x (P)))) (PreH51 : (afpoint_represents x_2 y_2 P )) (PreH52 : (afpoint_represents x y SM2_G_POINT )) (PreH53 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH54 : (id_len_pre <= 50)) (PreH55 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) bytes_4 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "charlist" ) ) + (96 * sizeof(UCHAR))) 32 bytes_4 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_12 := sm2_get_id_digest_partial_solve_wit_12_pure -> sm2_get_id_digest_partial_solve_wit_12_aux.

Definition sm2_get_id_digest_partial_solve_wit_13_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (u8_list_bounded (rev (bytes_4)) )) (PreH2 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH3 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_4)) = 32)) (PreH5 : (u8_list_bounded bytes_4 )) (PreH6 : (u8_list_bounded (rev (bytes_3)) )) (PreH7 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH8 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_3)) = 32)) (PreH10 : (u8_list_bounded bytes_3 )) (PreH11 : (u8_list_bounded (rev (bytes_6)) )) (PreH12 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH13 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_6)) = 32)) (PreH15 : (u8_list_bounded bytes_6 )) (PreH16 : (u8_list_bounded (rev (bytes_5)) )) (PreH17 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH18 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_5)) = 32)) (PreH20 : (u8_list_bounded bytes_5 )) (PreH21 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH22 : ((Zlength (ID)) = id_len_pre)) (PreH23 : (u8_list_bounded ID )) (PreH24 : ((2 + id_len_pre ) <= 250)) (PreH25 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH26 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH27 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH28 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH30 : ((u8_list_value (bytes_4)) = y)) (PreH31 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH32 : ((u8_list_value (bytes_3)) = x)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH34 : ((u8_list_value (bytes_2)) = y_2)) (PreH35 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH36 : ((u8_list_value (bytes)) = x_2)) (PreH37 : (x_2 < SM2_P_Z)) (PreH38 : (0 <= x_2)) (PreH39 : (y_2 < SM2_P_Z)) (PreH40 : (0 <= y_2)) (PreH41 : (x < SM2_P_Z)) (PreH42 : (0 <= x)) (PreH43 : (y < SM2_P_Z)) (PreH44 : (0 <= y)) (PreH45 : (SM2_A_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_A_Z)) (PreH47 : (SM2_B_Z < SM2_P_Z)) (PreH48 : (0 <= SM2_B_Z)) (PreH49 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH50 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH51 : (y_2 = (sm2_point_y (P)))) (PreH52 : (x_2 = (sm2_point_x (P)))) (PreH53 : (afpoint_represents x_2 y_2 P )) (PreH54 : (afpoint_represents x y SM2_G_POINT )) (PreH55 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH56 : (id_len_pre <= 50)) (PreH57 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (128 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (128 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 128) ” 
  &&  “ ((128 + 32 ) <= 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_13_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (PreH1 : (u8_list_bounded (rev (bytes_4)) )) (PreH2 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH3 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes_4)) = 32)) (PreH5 : (u8_list_bounded bytes_4 )) (PreH6 : (u8_list_bounded (rev (bytes_3)) )) (PreH7 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH8 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_3)) = 32)) (PreH10 : (u8_list_bounded bytes_3 )) (PreH11 : (u8_list_bounded (rev (bytes_6)) )) (PreH12 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH13 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_6)) = 32)) (PreH15 : (u8_list_bounded bytes_6 )) (PreH16 : (u8_list_bounded (rev (bytes_5)) )) (PreH17 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH18 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_5)) = 32)) (PreH20 : (u8_list_bounded bytes_5 )) (PreH21 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH22 : ((Zlength (ID)) = id_len_pre)) (PreH23 : (u8_list_bounded ID )) (PreH24 : ((2 + id_len_pre ) <= 250)) (PreH25 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH26 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH27 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH28 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH29 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH30 : ((u8_list_value (bytes_4)) = y)) (PreH31 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH32 : ((u8_list_value (bytes_3)) = x)) (PreH33 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH34 : ((u8_list_value (bytes_2)) = y_2)) (PreH35 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH36 : ((u8_list_value (bytes)) = x_2)) (PreH37 : (x_2 < SM2_P_Z)) (PreH38 : (0 <= x_2)) (PreH39 : (y_2 < SM2_P_Z)) (PreH40 : (0 <= y_2)) (PreH41 : (x < SM2_P_Z)) (PreH42 : (0 <= x)) (PreH43 : (y < SM2_P_Z)) (PreH44 : (0 <= y)) (PreH45 : (SM2_A_Z < SM2_P_Z)) (PreH46 : (0 <= SM2_A_Z)) (PreH47 : (SM2_B_Z < SM2_P_Z)) (PreH48 : (0 <= SM2_B_Z)) (PreH49 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH50 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH51 : (y_2 = (sm2_point_y (P)))) (PreH52 : (x_2 = (sm2_point_x (P)))) (PreH53 : (afpoint_represents x_2 y_2 P )) (PreH54 : (afpoint_represents x y SM2_G_POINT )) (PreH55 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH56 : (id_len_pre <= 50)) (PreH57 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (96 + 32 ) 192 )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (128 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (128 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 128) ” 
  &&  “ ((128 + 32 ) <= 192) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "charlist" ) ) 128 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_13 := sm2_get_id_digest_partial_solve_wit_13_pure -> sm2_get_id_digest_partial_solve_wit_13_aux.

Definition sm2_get_id_digest_partial_solve_wit_14_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes)) = 32)) (PreH3 : (u8_list_bounded bytes )) (PreH4 : (u8_list_bounded (rev (bytes_4)) )) (PreH5 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH6 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_4)) = 32)) (PreH8 : (u8_list_bounded bytes_4 )) (PreH9 : (u8_list_bounded (rev (bytes_3)) )) (PreH10 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH11 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_3)) = 32)) (PreH13 : (u8_list_bounded bytes_3 )) (PreH14 : (u8_list_bounded (rev (bytes_6)) )) (PreH15 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH16 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_6)) = 32)) (PreH18 : (u8_list_bounded bytes_6 )) (PreH19 : (u8_list_bounded (rev (bytes_5)) )) (PreH20 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH21 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_5)) = 32)) (PreH23 : (u8_list_bounded bytes_5 )) (PreH24 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH25 : ((Zlength (ID)) = id_len_pre)) (PreH26 : (u8_list_bounded ID )) (PreH27 : ((2 + id_len_pre ) <= 250)) (PreH28 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH29 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH30 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH31 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH32 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH33 : ((u8_list_value (bytes_4)) = y)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH35 : ((u8_list_value (bytes_3)) = x)) (PreH36 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH37 : ((u8_list_value (bytes_2)) = y_2)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH39 : ((u8_list_value (bytes)) = x_2)) (PreH40 : (x_2 < SM2_P_Z)) (PreH41 : (0 <= x_2)) (PreH42 : (y_2 < SM2_P_Z)) (PreH43 : (0 <= y_2)) (PreH44 : (x < SM2_P_Z)) (PreH45 : (0 <= x)) (PreH46 : (y < SM2_P_Z)) (PreH47 : (0 <= y)) (PreH48 : (SM2_A_Z < SM2_P_Z)) (PreH49 : (0 <= SM2_A_Z)) (PreH50 : (SM2_B_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_B_Z)) (PreH52 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH53 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH54 : (y_2 = (sm2_point_y (P)))) (PreH55 : (x_2 = (sm2_point_x (P)))) (PreH56 : (afpoint_represents x_2 y_2 P )) (PreH57 : (afpoint_represents x y SM2_G_POINT )) (PreH58 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH59 : (id_len_pre <= 50)) (PreH60 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) bytes )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ”
.

Definition sm2_get_id_digest_partial_solve_wit_14_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes)) = 32)) (PreH3 : (u8_list_bounded bytes )) (PreH4 : (u8_list_bounded (rev (bytes_4)) )) (PreH5 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH6 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_4)) = 32)) (PreH8 : (u8_list_bounded bytes_4 )) (PreH9 : (u8_list_bounded (rev (bytes_3)) )) (PreH10 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH11 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_3)) = 32)) (PreH13 : (u8_list_bounded bytes_3 )) (PreH14 : (u8_list_bounded (rev (bytes_6)) )) (PreH15 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH16 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_6)) = 32)) (PreH18 : (u8_list_bounded bytes_6 )) (PreH19 : (u8_list_bounded (rev (bytes_5)) )) (PreH20 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH21 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_5)) = 32)) (PreH23 : (u8_list_bounded bytes_5 )) (PreH24 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH25 : ((Zlength (ID)) = id_len_pre)) (PreH26 : (u8_list_bounded ID )) (PreH27 : ((2 + id_len_pre ) <= 250)) (PreH28 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH29 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH30 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH31 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH32 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH33 : ((u8_list_value (bytes_4)) = y)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH35 : ((u8_list_value (bytes_3)) = x)) (PreH36 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH37 : ((u8_list_value (bytes_2)) = y_2)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH39 : ((u8_list_value (bytes)) = x_2)) (PreH40 : (x_2 < SM2_P_Z)) (PreH41 : (0 <= x_2)) (PreH42 : (y_2 < SM2_P_Z)) (PreH43 : (0 <= y_2)) (PreH44 : (x < SM2_P_Z)) (PreH45 : (0 <= x)) (PreH46 : (y < SM2_P_Z)) (PreH47 : (0 <= y)) (PreH48 : (SM2_A_Z < SM2_P_Z)) (PreH49 : (0 <= SM2_A_Z)) (PreH50 : (SM2_B_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_B_Z)) (PreH52 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH53 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH54 : (y_2 = (sm2_point_y (P)))) (PreH55 : (x_2 = (sm2_point_x (P)))) (PreH56 : (afpoint_represents x_2 y_2 P )) (PreH57 : (afpoint_represents x y SM2_G_POINT )) (PreH58 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH59 : (id_len_pre <= 50)) (PreH60 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) bytes )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "charlist" ) ) + (128 * sizeof(UCHAR))) 32 bytes )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_14 := sm2_get_id_digest_partial_solve_wit_14_pure -> sm2_get_id_digest_partial_solve_wit_14_aux.

Definition sm2_get_id_digest_partial_solve_wit_15_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (u8_list_bounded (rev (bytes)) )) (PreH2 : ((Zlength ((rev (bytes)))) = 32)) (PreH3 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes)) = 32)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (u8_list_bounded (rev (bytes_4)) )) (PreH7 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH8 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_4)) = 32)) (PreH10 : (u8_list_bounded bytes_4 )) (PreH11 : (u8_list_bounded (rev (bytes_3)) )) (PreH12 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH13 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_3)) = 32)) (PreH15 : (u8_list_bounded bytes_3 )) (PreH16 : (u8_list_bounded (rev (bytes_6)) )) (PreH17 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH18 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_6)) = 32)) (PreH20 : (u8_list_bounded bytes_6 )) (PreH21 : (u8_list_bounded (rev (bytes_5)) )) (PreH22 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH23 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_5)) = 32)) (PreH25 : (u8_list_bounded bytes_5 )) (PreH26 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH27 : ((Zlength (ID)) = id_len_pre)) (PreH28 : (u8_list_bounded ID )) (PreH29 : ((2 + id_len_pre ) <= 250)) (PreH30 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH31 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH32 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH33 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH35 : ((u8_list_value (bytes_4)) = y)) (PreH36 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH37 : ((u8_list_value (bytes_3)) = x)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH39 : ((u8_list_value (bytes_2)) = y_2)) (PreH40 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH41 : ((u8_list_value (bytes)) = x_2)) (PreH42 : (x_2 < SM2_P_Z)) (PreH43 : (0 <= x_2)) (PreH44 : (y_2 < SM2_P_Z)) (PreH45 : (0 <= y_2)) (PreH46 : (x < SM2_P_Z)) (PreH47 : (0 <= x)) (PreH48 : (y < SM2_P_Z)) (PreH49 : (0 <= y)) (PreH50 : (SM2_A_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_A_Z)) (PreH52 : (SM2_B_Z < SM2_P_Z)) (PreH53 : (0 <= SM2_B_Z)) (PreH54 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH55 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH56 : (y_2 = (sm2_point_y (P)))) (PreH57 : (x_2 = (sm2_point_x (P)))) (PreH58 : (afpoint_represents x_2 y_2 P )) (PreH59 : (afpoint_represents x y SM2_G_POINT )) (PreH60 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH61 : (id_len_pre <= 50)) (PreH62 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (160 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (160 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 160) ” 
  &&  “ ((160 + 32 ) <= 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_15_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (PreH1 : (u8_list_bounded (rev (bytes)) )) (PreH2 : ((Zlength ((rev (bytes)))) = 32)) (PreH3 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH4 : ((Zlength (bytes)) = 32)) (PreH5 : (u8_list_bounded bytes )) (PreH6 : (u8_list_bounded (rev (bytes_4)) )) (PreH7 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH8 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH9 : ((Zlength (bytes_4)) = 32)) (PreH10 : (u8_list_bounded bytes_4 )) (PreH11 : (u8_list_bounded (rev (bytes_3)) )) (PreH12 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH13 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH14 : ((Zlength (bytes_3)) = 32)) (PreH15 : (u8_list_bounded bytes_3 )) (PreH16 : (u8_list_bounded (rev (bytes_6)) )) (PreH17 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH18 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH19 : ((Zlength (bytes_6)) = 32)) (PreH20 : (u8_list_bounded bytes_6 )) (PreH21 : (u8_list_bounded (rev (bytes_5)) )) (PreH22 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH23 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH24 : ((Zlength (bytes_5)) = 32)) (PreH25 : (u8_list_bounded bytes_5 )) (PreH26 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH27 : ((Zlength (ID)) = id_len_pre)) (PreH28 : (u8_list_bounded ID )) (PreH29 : ((2 + id_len_pre ) <= 250)) (PreH30 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH31 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH32 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH33 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH34 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH35 : ((u8_list_value (bytes_4)) = y)) (PreH36 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH37 : ((u8_list_value (bytes_3)) = x)) (PreH38 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH39 : ((u8_list_value (bytes_2)) = y_2)) (PreH40 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH41 : ((u8_list_value (bytes)) = x_2)) (PreH42 : (x_2 < SM2_P_Z)) (PreH43 : (0 <= x_2)) (PreH44 : (y_2 < SM2_P_Z)) (PreH45 : (0 <= y_2)) (PreH46 : (x < SM2_P_Z)) (PreH47 : (0 <= x)) (PreH48 : (y < SM2_P_Z)) (PreH49 : (0 <= y)) (PreH50 : (SM2_A_Z < SM2_P_Z)) (PreH51 : (0 <= SM2_A_Z)) (PreH52 : (SM2_B_Z < SM2_P_Z)) (PreH53 : (0 <= SM2_B_Z)) (PreH54 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH55 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH56 : (y_2 = (sm2_point_y (P)))) (PreH57 : (x_2 = (sm2_point_x (P)))) (PreH58 : (afpoint_represents x_2 y_2 P )) (PreH59 : (afpoint_represents x y SM2_G_POINT )) (PreH60 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH61 : (id_len_pre <= 50)) (PreH62 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (128 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "charlist" ) ) + (160 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (160 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 32) ” 
  &&  “ (0 <= 160) ” 
  &&  “ ((160 + 32 ) <= 192) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "charlist" ) ) 160 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_15 := sm2_get_id_digest_partial_solve_wit_15_pure -> sm2_get_id_digest_partial_solve_wit_15_aux.

Definition sm2_get_id_digest_partial_solve_wit_16_pure := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_2)) = 32)) (PreH3 : (u8_list_bounded bytes_2 )) (PreH4 : (u8_list_bounded (rev (bytes)) )) (PreH5 : ((Zlength ((rev (bytes)))) = 32)) (PreH6 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes)) = 32)) (PreH8 : (u8_list_bounded bytes )) (PreH9 : (u8_list_bounded (rev (bytes_4)) )) (PreH10 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH11 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_4)) = 32)) (PreH13 : (u8_list_bounded bytes_4 )) (PreH14 : (u8_list_bounded (rev (bytes_3)) )) (PreH15 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH16 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_3)) = 32)) (PreH18 : (u8_list_bounded bytes_3 )) (PreH19 : (u8_list_bounded (rev (bytes_6)) )) (PreH20 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH21 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_6)) = 32)) (PreH23 : (u8_list_bounded bytes_6 )) (PreH24 : (u8_list_bounded (rev (bytes_5)) )) (PreH25 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH26 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_5)) = 32)) (PreH28 : (u8_list_bounded bytes_5 )) (PreH29 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH30 : ((Zlength (ID)) = id_len_pre)) (PreH31 : (u8_list_bounded ID )) (PreH32 : ((2 + id_len_pre ) <= 250)) (PreH33 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH34 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH35 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH36 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH37 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH38 : ((u8_list_value (bytes_4)) = y)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH40 : ((u8_list_value (bytes_3)) = x)) (PreH41 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH42 : ((u8_list_value (bytes_2)) = y_2)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH44 : ((u8_list_value (bytes)) = x_2)) (PreH45 : (x_2 < SM2_P_Z)) (PreH46 : (0 <= x_2)) (PreH47 : (y_2 < SM2_P_Z)) (PreH48 : (0 <= y_2)) (PreH49 : (x < SM2_P_Z)) (PreH50 : (0 <= x)) (PreH51 : (y < SM2_P_Z)) (PreH52 : (0 <= y)) (PreH53 : (SM2_A_Z < SM2_P_Z)) (PreH54 : (0 <= SM2_A_Z)) (PreH55 : (SM2_B_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_B_Z)) (PreH57 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH58 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH59 : (y_2 = (sm2_point_y (P)))) (PreH60 : (x_2 = (sm2_point_x (P)))) (PreH61 : (afpoint_represents x_2 y_2 P )) (PreH62 : (afpoint_represents x y SM2_G_POINT )) (PreH63 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH64 : (id_len_pre <= 50)) (PreH65 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) bytes_2 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (160 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ”
.

Definition sm2_get_id_digest_partial_solve_wit_16_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH2 : ((Zlength (bytes_2)) = 32)) (PreH3 : (u8_list_bounded bytes_2 )) (PreH4 : (u8_list_bounded (rev (bytes)) )) (PreH5 : ((Zlength ((rev (bytes)))) = 32)) (PreH6 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes)) = 32)) (PreH8 : (u8_list_bounded bytes )) (PreH9 : (u8_list_bounded (rev (bytes_4)) )) (PreH10 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH11 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes_4)) = 32)) (PreH13 : (u8_list_bounded bytes_4 )) (PreH14 : (u8_list_bounded (rev (bytes_3)) )) (PreH15 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH16 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_3)) = 32)) (PreH18 : (u8_list_bounded bytes_3 )) (PreH19 : (u8_list_bounded (rev (bytes_6)) )) (PreH20 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH21 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_6)) = 32)) (PreH23 : (u8_list_bounded bytes_6 )) (PreH24 : (u8_list_bounded (rev (bytes_5)) )) (PreH25 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH26 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_5)) = 32)) (PreH28 : (u8_list_bounded bytes_5 )) (PreH29 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH30 : ((Zlength (ID)) = id_len_pre)) (PreH31 : (u8_list_bounded ID )) (PreH32 : ((2 + id_len_pre ) <= 250)) (PreH33 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH34 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH35 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH36 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH37 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH38 : ((u8_list_value (bytes_4)) = y)) (PreH39 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH40 : ((u8_list_value (bytes_3)) = x)) (PreH41 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH42 : ((u8_list_value (bytes_2)) = y_2)) (PreH43 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH44 : ((u8_list_value (bytes)) = x_2)) (PreH45 : (x_2 < SM2_P_Z)) (PreH46 : (0 <= x_2)) (PreH47 : (y_2 < SM2_P_Z)) (PreH48 : (0 <= y_2)) (PreH49 : (x < SM2_P_Z)) (PreH50 : (0 <= x)) (PreH51 : (y < SM2_P_Z)) (PreH52 : (0 <= y)) (PreH53 : (SM2_A_Z < SM2_P_Z)) (PreH54 : (0 <= SM2_A_Z)) (PreH55 : (SM2_B_Z < SM2_P_Z)) (PreH56 : (0 <= SM2_B_Z)) (PreH57 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH58 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH59 : (y_2 = (sm2_point_y (P)))) (PreH60 : (x_2 = (sm2_point_x (P)))) (PreH61 : (afpoint_represents x_2 y_2 P )) (PreH62 : (afpoint_represents x y SM2_G_POINT )) (PreH63 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH64 : (id_len_pre <= 50)) (PreH65 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (UCharArray.seg ( &( "charlist" ) ) 160 (160 + 32 ) bytes_2 )
  **  (UCharArray.undef_seg ( &( "charlist" ) ) (160 + 32 ) 192 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (0 < 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "charlist" ) ) + (160 * sizeof(UCHAR))) 32 bytes_2 )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "y") 32 bytes_2 )
  **  (UCharArray.seg ( &( "charlist" ) ) 128 (128 + 32 ) (rev (bytes)) )
  **  (store_bytes &((pubkey_pre)  # "AFPoint" ->ₛ "x") 32 bytes )
  **  (UCharArray.seg ( &( "charlist" ) ) 96 (96 + 32 ) (rev (bytes_4)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "y") 32 bytes_4 )
  **  (UCharArray.seg ( &( "charlist" ) ) 64 (64 + 32 ) (rev (bytes_3)) )
  **  (store_bytes &(( &( "SM2_G" ) )->ₛ "x") 32 bytes_3 )
  **  (UCharArray.seg ( &( "charlist" ) ) 32 (32 + 32 ) (rev (bytes_6)) )
  **  (store_bytes ( &( "SM2_b" ) ) 32 bytes_6 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 32 ) (rev (bytes_5)) )
  **  (store_bytes ( &( "SM2_a" ) ) 32 bytes_5 )
  **  (UCharArray.seg ( &( "total" ) ) 2 (2 + id_len_pre ) ID )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (UCharArray.seg ( &( "total" ) ) 0 2 (sm2_entla_bytes (id_len_pre)) )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_16 := sm2_get_id_digest_partial_solve_wit_16_pure -> sm2_get_id_digest_partial_solve_wit_16_aux.

Definition sm2_get_id_digest_partial_solve_wit_17_pure := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH2 : (u8_list_bounded (rev (bytes_2)) )) (PreH3 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH4 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH5 : ((Zlength (bytes_2)) = 32)) (PreH6 : (u8_list_bounded bytes_2 )) (PreH7 : (u8_list_bounded (rev (bytes)) )) (PreH8 : ((Zlength ((rev (bytes)))) = 32)) (PreH9 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes)) = 32)) (PreH11 : (u8_list_bounded bytes )) (PreH12 : (u8_list_bounded (rev (bytes_4)) )) (PreH13 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH14 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes_4)) = 32)) (PreH16 : (u8_list_bounded bytes_4 )) (PreH17 : (u8_list_bounded (rev (bytes_3)) )) (PreH18 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH19 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_3)) = 32)) (PreH21 : (u8_list_bounded bytes_3 )) (PreH22 : (u8_list_bounded (rev (bytes_6)) )) (PreH23 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH24 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_6)) = 32)) (PreH26 : (u8_list_bounded bytes_6 )) (PreH27 : (u8_list_bounded (rev (bytes_5)) )) (PreH28 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH29 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_5)) = 32)) (PreH31 : (u8_list_bounded bytes_5 )) (PreH32 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH33 : ((Zlength (ID)) = id_len_pre)) (PreH34 : (u8_list_bounded ID )) (PreH35 : ((2 + id_len_pre ) <= 250)) (PreH36 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH37 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH38 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH39 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH40 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH41 : ((u8_list_value (bytes_4)) = y)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH43 : ((u8_list_value (bytes_3)) = x)) (PreH44 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_2)) = y_2)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH47 : ((u8_list_value (bytes)) = x_2)) (PreH48 : (x_2 < SM2_P_Z)) (PreH49 : (0 <= x_2)) (PreH50 : (y_2 < SM2_P_Z)) (PreH51 : (0 <= y_2)) (PreH52 : (x < SM2_P_Z)) (PreH53 : (0 <= x)) (PreH54 : (y < SM2_P_Z)) (PreH55 : (0 <= y)) (PreH56 : (SM2_A_Z < SM2_P_Z)) (PreH57 : (0 <= SM2_A_Z)) (PreH58 : (SM2_B_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_B_Z)) (PreH60 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH61 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH62 : (y_2 = (sm2_point_y (P)))) (PreH63 : (x_2 = (sm2_point_x (P)))) (PreH64 : (afpoint_represents x_2 y_2 P )) (PreH65 : (afpoint_represents x y SM2_G_POINT )) (PreH66 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH67 : (id_len_pre <= 50)) (PreH68 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))) = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ ((( &( "charlist" ) ) + (0 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 192) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))) ) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = 192) ” 
  &&  “ (0 <= (2 + id_len_pre )) ” 
  &&  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ”
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))) ) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))) ) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = 192) ” 
  &&  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ”
).

Definition sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ”
.

Definition sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_3 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))) ) ”
.

Definition sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_4 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))) ) ”
.

Definition sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_5 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = 192) ”
.

Definition sm2_get_id_digest_partial_solve_wit_17_pure_split_goal_6 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH4 : (u8_list_bounded (rev (bytes_2)) )) (PreH5 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH6 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH7 : ((Zlength (bytes_2)) = 32)) (PreH8 : (u8_list_bounded bytes_2 )) (PreH9 : (u8_list_bounded (rev (bytes)) )) (PreH10 : ((Zlength ((rev (bytes)))) = 32)) (PreH11 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH12 : ((Zlength (bytes)) = 32)) (PreH13 : (u8_list_bounded bytes )) (PreH14 : (u8_list_bounded (rev (bytes_4)) )) (PreH15 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH16 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH17 : ((Zlength (bytes_4)) = 32)) (PreH18 : (u8_list_bounded bytes_4 )) (PreH19 : (u8_list_bounded (rev (bytes_3)) )) (PreH20 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH21 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH22 : ((Zlength (bytes_3)) = 32)) (PreH23 : (u8_list_bounded bytes_3 )) (PreH24 : (u8_list_bounded (rev (bytes_6)) )) (PreH25 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH26 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH27 : ((Zlength (bytes_6)) = 32)) (PreH28 : (u8_list_bounded bytes_6 )) (PreH29 : (u8_list_bounded (rev (bytes_5)) )) (PreH30 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH31 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH32 : ((Zlength (bytes_5)) = 32)) (PreH33 : (u8_list_bounded bytes_5 )) (PreH34 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH35 : ((Zlength (ID)) = id_len_pre)) (PreH36 : (u8_list_bounded ID )) (PreH37 : ((2 + id_len_pre ) <= 250)) (PreH38 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH39 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH40 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH41 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH43 : ((u8_list_value (bytes_4)) = y)) (PreH44 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH45 : ((u8_list_value (bytes_3)) = x)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH47 : ((u8_list_value (bytes_2)) = y_2)) (PreH48 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH49 : ((u8_list_value (bytes)) = x_2)) (PreH50 : (x_2 < SM2_P_Z)) (PreH51 : (0 <= x_2)) (PreH52 : (y_2 < SM2_P_Z)) (PreH53 : (0 <= y_2)) (PreH54 : (x < SM2_P_Z)) (PreH55 : (0 <= x)) (PreH56 : (y < SM2_P_Z)) (PreH57 : (0 <= y)) (PreH58 : (SM2_A_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_A_Z)) (PreH60 : (SM2_B_Z < SM2_P_Z)) (PreH61 : (0 <= SM2_B_Z)) (PreH62 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH63 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH64 : (y_2 = (sm2_point_y (P)))) (PreH65 : (x_2 = (sm2_point_x (P)))) (PreH66 : (afpoint_represents x_2 y_2 P )) (PreH67 : (afpoint_represents x y SM2_G_POINT )) (PreH68 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH69 : (id_len_pre <= 50)) (PreH70 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ”
.

Definition sm2_get_id_digest_partial_solve_wit_17_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (PreH1 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH2 : (u8_list_bounded (rev (bytes_2)) )) (PreH3 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH4 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH5 : ((Zlength (bytes_2)) = 32)) (PreH6 : (u8_list_bounded bytes_2 )) (PreH7 : (u8_list_bounded (rev (bytes)) )) (PreH8 : ((Zlength ((rev (bytes)))) = 32)) (PreH9 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes)) = 32)) (PreH11 : (u8_list_bounded bytes )) (PreH12 : (u8_list_bounded (rev (bytes_4)) )) (PreH13 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH14 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes_4)) = 32)) (PreH16 : (u8_list_bounded bytes_4 )) (PreH17 : (u8_list_bounded (rev (bytes_3)) )) (PreH18 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH19 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_3)) = 32)) (PreH21 : (u8_list_bounded bytes_3 )) (PreH22 : (u8_list_bounded (rev (bytes_6)) )) (PreH23 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH24 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_6)) = 32)) (PreH26 : (u8_list_bounded bytes_6 )) (PreH27 : (u8_list_bounded (rev (bytes_5)) )) (PreH28 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH29 : (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_5)) = 32)) (PreH31 : (u8_list_bounded bytes_5 )) (PreH32 : (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH33 : ((Zlength (ID)) = id_len_pre)) (PreH34 : (u8_list_bounded ID )) (PreH35 : ((2 + id_len_pre ) <= 250)) (PreH36 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH37 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH38 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH39 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH40 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH41 : ((u8_list_value (bytes_4)) = y)) (PreH42 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH43 : ((u8_list_value (bytes_3)) = x)) (PreH44 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH45 : ((u8_list_value (bytes_2)) = y_2)) (PreH46 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH47 : ((u8_list_value (bytes)) = x_2)) (PreH48 : (x_2 < SM2_P_Z)) (PreH49 : (0 <= x_2)) (PreH50 : (y_2 < SM2_P_Z)) (PreH51 : (0 <= y_2)) (PreH52 : (x < SM2_P_Z)) (PreH53 : (0 <= x)) (PreH54 : (y < SM2_P_Z)) (PreH55 : (0 <= y)) (PreH56 : (SM2_A_Z < SM2_P_Z)) (PreH57 : (0 <= SM2_A_Z)) (PreH58 : (SM2_B_Z < SM2_P_Z)) (PreH59 : (0 <= SM2_B_Z)) (PreH60 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH61 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH62 : (y_2 = (sm2_point_y (P)))) (PreH63 : (x_2 = (sm2_point_x (P)))) (PreH64 : (afpoint_represents x_2 y_2 P )) (PreH65 : (afpoint_represents x y SM2_G_POINT )) (PreH66 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH67 : (id_len_pre <= 50)) (PreH68 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 192 (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ ((( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))) = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ ((( &( "charlist" ) ) + (0 * sizeof(UCHAR))) = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= 192) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))) ) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes (x))) ((app ((u256_to_be_bytes (y))) ((app ((u256_to_be_bytes (x_2))) ((u256_to_be_bytes (y_2)))))))))))))) = 192) ” 
  &&  “ (0 <= (2 + id_len_pre )) ” 
  &&  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval_2 = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (UCharArray.undef_seg ( &( "total" ) ) (2 + id_len_pre ) 250 )
  **  (UCharArray.seg ( &( "charlist" ) ) 0 (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (UCharArray.seg ( &( "total" ) ) 0 (2 + id_len_pre ) (app ((sm2_entla_bytes (id_len_pre))) (ID)) )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
.

Definition sm2_get_id_digest_partial_solve_wit_17 := sm2_get_id_digest_partial_solve_wit_17_pure -> sm2_get_id_digest_partial_solve_wit_17_aux.

Definition sm2_get_id_digest_partial_solve_wit_18_pure := 
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 result_pre ) ” 
  &&  “ (sm3_digest_input_aligned (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) ) ”
) \/
(
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH4 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH5 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH6 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH7 : (u8_list_bounded (rev (bytes_2)) )) (PreH8 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH9 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes_2)) = 32)) (PreH11 : (u8_list_bounded bytes_2 )) (PreH12 : (u8_list_bounded (rev (bytes)) )) (PreH13 : ((Zlength ((rev (bytes)))) = 32)) (PreH14 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes)) = 32)) (PreH16 : (u8_list_bounded bytes )) (PreH17 : (u8_list_bounded (rev (bytes_4)) )) (PreH18 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH19 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_4)) = 32)) (PreH21 : (u8_list_bounded bytes_4 )) (PreH22 : (u8_list_bounded (rev (bytes_3)) )) (PreH23 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH24 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_3)) = 32)) (PreH26 : (u8_list_bounded bytes_3 )) (PreH27 : (u8_list_bounded (rev (bytes_6)) )) (PreH28 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH29 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_6)) = 32)) (PreH31 : (u8_list_bounded bytes_6 )) (PreH32 : (u8_list_bounded (rev (bytes_5)) )) (PreH33 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH34 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH35 : ((Zlength (bytes_5)) = 32)) (PreH36 : (u8_list_bounded bytes_5 )) (PreH37 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH38 : ((Zlength (ID)) = id_len_pre)) (PreH39 : (u8_list_bounded ID )) (PreH40 : ((2 + id_len_pre ) <= 250)) (PreH41 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH42 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH43 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH44 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH46 : ((u8_list_value (bytes_4)) = y)) (PreH47 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH48 : ((u8_list_value (bytes_3)) = x)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH50 : ((u8_list_value (bytes_2)) = y_2)) (PreH51 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH52 : ((u8_list_value (bytes)) = x_2)) (PreH53 : (x_2 < SM2_P_Z)) (PreH54 : (0 <= x_2)) (PreH55 : (y_2 < SM2_P_Z)) (PreH56 : (0 <= y_2)) (PreH57 : (x < SM2_P_Z)) (PreH58 : (0 <= x)) (PreH59 : (y < SM2_P_Z)) (PreH60 : (0 <= y)) (PreH61 : (SM2_A_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_A_Z)) (PreH63 : (SM2_B_Z < SM2_P_Z)) (PreH64 : (0 <= SM2_B_Z)) (PreH65 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH66 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH67 : (y_2 = (sm2_point_y (P)))) (PreH68 : (x_2 = (sm2_point_x (P)))) (PreH69 : (afpoint_represents x_2 y_2 P )) (PreH70 : (afpoint_represents x y SM2_G_POINT )) (PreH71 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH72 : (id_len_pre <= 50)) (PreH73 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (sm3_digest_input_aligned (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) ) ” 
  &&  “ (aligned_4 result_pre ) ”
).

Definition sm2_get_id_digest_partial_solve_wit_18_pure_split_goal_1 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH4 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH5 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH6 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH7 : (u8_list_bounded (rev (bytes_2)) )) (PreH8 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH9 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes_2)) = 32)) (PreH11 : (u8_list_bounded bytes_2 )) (PreH12 : (u8_list_bounded (rev (bytes)) )) (PreH13 : ((Zlength ((rev (bytes)))) = 32)) (PreH14 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes)) = 32)) (PreH16 : (u8_list_bounded bytes )) (PreH17 : (u8_list_bounded (rev (bytes_4)) )) (PreH18 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH19 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_4)) = 32)) (PreH21 : (u8_list_bounded bytes_4 )) (PreH22 : (u8_list_bounded (rev (bytes_3)) )) (PreH23 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH24 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_3)) = 32)) (PreH26 : (u8_list_bounded bytes_3 )) (PreH27 : (u8_list_bounded (rev (bytes_6)) )) (PreH28 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH29 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_6)) = 32)) (PreH31 : (u8_list_bounded bytes_6 )) (PreH32 : (u8_list_bounded (rev (bytes_5)) )) (PreH33 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH34 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH35 : ((Zlength (bytes_5)) = 32)) (PreH36 : (u8_list_bounded bytes_5 )) (PreH37 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH38 : ((Zlength (ID)) = id_len_pre)) (PreH39 : (u8_list_bounded ID )) (PreH40 : ((2 + id_len_pre ) <= 250)) (PreH41 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH42 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH43 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH44 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH46 : ((u8_list_value (bytes_4)) = y)) (PreH47 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH48 : ((u8_list_value (bytes_3)) = x)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH50 : ((u8_list_value (bytes_2)) = y_2)) (PreH51 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH52 : ((u8_list_value (bytes)) = x_2)) (PreH53 : (x_2 < SM2_P_Z)) (PreH54 : (0 <= x_2)) (PreH55 : (y_2 < SM2_P_Z)) (PreH56 : (0 <= y_2)) (PreH57 : (x < SM2_P_Z)) (PreH58 : (0 <= x)) (PreH59 : (y < SM2_P_Z)) (PreH60 : (0 <= y)) (PreH61 : (SM2_A_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_A_Z)) (PreH63 : (SM2_B_Z < SM2_P_Z)) (PreH64 : (0 <= SM2_B_Z)) (PreH65 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH66 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH67 : (y_2 = (sm2_point_y (P)))) (PreH68 : (x_2 = (sm2_point_x (P)))) (PreH69 : (afpoint_represents x_2 y_2 P )) (PreH70 : (afpoint_represents x y SM2_G_POINT )) (PreH71 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH72 : (id_len_pre <= 50)) (PreH73 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (sm3_digest_input_aligned (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) ) ”
.

Definition sm2_get_id_digest_partial_solve_wit_18_pure_split_goal_2 := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (id_len_pre <= UINT64_MAX)) (PreH2 : (id_len_pre >= 0)) (PreH3 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH4 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH5 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH6 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH7 : (u8_list_bounded (rev (bytes_2)) )) (PreH8 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH9 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH10 : ((Zlength (bytes_2)) = 32)) (PreH11 : (u8_list_bounded bytes_2 )) (PreH12 : (u8_list_bounded (rev (bytes)) )) (PreH13 : ((Zlength ((rev (bytes)))) = 32)) (PreH14 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH15 : ((Zlength (bytes)) = 32)) (PreH16 : (u8_list_bounded bytes )) (PreH17 : (u8_list_bounded (rev (bytes_4)) )) (PreH18 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH19 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH20 : ((Zlength (bytes_4)) = 32)) (PreH21 : (u8_list_bounded bytes_4 )) (PreH22 : (u8_list_bounded (rev (bytes_3)) )) (PreH23 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH24 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH25 : ((Zlength (bytes_3)) = 32)) (PreH26 : (u8_list_bounded bytes_3 )) (PreH27 : (u8_list_bounded (rev (bytes_6)) )) (PreH28 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH29 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH30 : ((Zlength (bytes_6)) = 32)) (PreH31 : (u8_list_bounded bytes_6 )) (PreH32 : (u8_list_bounded (rev (bytes_5)) )) (PreH33 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH34 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH35 : ((Zlength (bytes_5)) = 32)) (PreH36 : (u8_list_bounded bytes_5 )) (PreH37 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH38 : ((Zlength (ID)) = id_len_pre)) (PreH39 : (u8_list_bounded ID )) (PreH40 : ((2 + id_len_pre ) <= 250)) (PreH41 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH42 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH43 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH44 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH46 : ((u8_list_value (bytes_4)) = y)) (PreH47 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH48 : ((u8_list_value (bytes_3)) = x)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH50 : ((u8_list_value (bytes_2)) = y_2)) (PreH51 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH52 : ((u8_list_value (bytes)) = x_2)) (PreH53 : (x_2 < SM2_P_Z)) (PreH54 : (0 <= x_2)) (PreH55 : (y_2 < SM2_P_Z)) (PreH56 : (0 <= y_2)) (PreH57 : (x < SM2_P_Z)) (PreH58 : (0 <= x)) (PreH59 : (y < SM2_P_Z)) (PreH60 : (0 <= y)) (PreH61 : (SM2_A_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_A_Z)) (PreH63 : (SM2_B_Z < SM2_P_Z)) (PreH64 : (0 <= SM2_B_Z)) (PreH65 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH66 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH67 : (y_2 = (sm2_point_y (P)))) (PreH68 : (x_2 = (sm2_point_x (P)))) (PreH69 : (afpoint_represents x_2 y_2 P )) (PreH70 : (afpoint_represents x y SM2_G_POINT )) (PreH71 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH72 : (id_len_pre <= 50)) (PreH73 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  ((( &( "id_len" ) )) # UInt64  |-> id_len_pre)
  **  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "id" ) )) # Ptr  |-> id_pre)
  **  ((( &( "pubkey" ) )) # Ptr  |-> pubkey_pre)
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 result_pre ) ”
.

Definition sm2_get_id_digest_partial_solve_wit_18_aux := 
forall (pubkey_pre: Z) (id_len_pre: Z) (id_pre: Z) (result_pre: Z) (P: ec_point) (ID: (@list Z)) (x: Z) (y: Z) (x_2: Z) (y_2: Z) (bytes: (@list Z)) (bytes_2: (@list Z)) (bytes_3: (@list Z)) (bytes_4: (@list Z)) (bytes_5: (@list Z)) (bytes_6: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (retval_5: Z) (retval_6: Z) (retval_7: Z) (retval_8: Z) (PreH1 : (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR))))) (PreH2 : ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192)) (PreH3 : (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )) (PreH4 : (((2 + id_len_pre ) + 192 ) <= 250)) (PreH5 : (u8_list_bounded (rev (bytes_2)) )) (PreH6 : ((Zlength ((rev (bytes_2)))) = 32)) (PreH7 : (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR))))) (PreH8 : ((Zlength (bytes_2)) = 32)) (PreH9 : (u8_list_bounded bytes_2 )) (PreH10 : (u8_list_bounded (rev (bytes)) )) (PreH11 : ((Zlength ((rev (bytes)))) = 32)) (PreH12 : (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR))))) (PreH13 : ((Zlength (bytes)) = 32)) (PreH14 : (u8_list_bounded bytes )) (PreH15 : (u8_list_bounded (rev (bytes_4)) )) (PreH16 : ((Zlength ((rev (bytes_4)))) = 32)) (PreH17 : (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR))))) (PreH18 : ((Zlength (bytes_4)) = 32)) (PreH19 : (u8_list_bounded bytes_4 )) (PreH20 : (u8_list_bounded (rev (bytes_3)) )) (PreH21 : ((Zlength ((rev (bytes_3)))) = 32)) (PreH22 : (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR))))) (PreH23 : ((Zlength (bytes_3)) = 32)) (PreH24 : (u8_list_bounded bytes_3 )) (PreH25 : (u8_list_bounded (rev (bytes_6)) )) (PreH26 : ((Zlength ((rev (bytes_6)))) = 32)) (PreH27 : (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR))))) (PreH28 : ((Zlength (bytes_6)) = 32)) (PreH29 : (u8_list_bounded bytes_6 )) (PreH30 : (u8_list_bounded (rev (bytes_5)) )) (PreH31 : ((Zlength ((rev (bytes_5)))) = 32)) (PreH32 : (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR))))) (PreH33 : ((Zlength (bytes_5)) = 32)) (PreH34 : (u8_list_bounded bytes_5 )) (PreH35 : (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR))))) (PreH36 : ((Zlength (ID)) = id_len_pre)) (PreH37 : (u8_list_bounded ID )) (PreH38 : ((2 + id_len_pre ) <= 250)) (PreH39 : (aligned_4 ( &( "SM2_b" ) ) )) (PreH40 : ((u8_list_value (bytes_6)) = SM2_B_Z)) (PreH41 : (aligned_4 ( &( "SM2_a" ) ) )) (PreH42 : ((u8_list_value (bytes_5)) = SM2_A_Z)) (PreH43 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") )) (PreH44 : ((u8_list_value (bytes_4)) = y)) (PreH45 : (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") )) (PreH46 : ((u8_list_value (bytes_3)) = x)) (PreH47 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") )) (PreH48 : ((u8_list_value (bytes_2)) = y_2)) (PreH49 : (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") )) (PreH50 : ((u8_list_value (bytes)) = x_2)) (PreH51 : (x_2 < SM2_P_Z)) (PreH52 : (0 <= x_2)) (PreH53 : (y_2 < SM2_P_Z)) (PreH54 : (0 <= y_2)) (PreH55 : (x < SM2_P_Z)) (PreH56 : (0 <= x)) (PreH57 : (y < SM2_P_Z)) (PreH58 : (0 <= y)) (PreH59 : (SM2_A_Z < SM2_P_Z)) (PreH60 : (0 <= SM2_A_Z)) (PreH61 : (SM2_B_Z < SM2_P_Z)) (PreH62 : (0 <= SM2_B_Z)) (PreH63 : (y = (sm2_point_y (SM2_G_POINT)))) (PreH64 : (x = (sm2_point_x (SM2_G_POINT)))) (PreH65 : (y_2 = (sm2_point_y (P)))) (PreH66 : (x_2 = (sm2_point_x (P)))) (PreH67 : (afpoint_represents x_2 y_2 P )) (PreH68 : (afpoint_represents x y SM2_G_POINT )) (PreH69 : (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) )) (PreH70 : (id_len_pre <= 50)) (PreH71 : (sm2_id_digest_output_aligned result_pre id_len_pre )) ,
  (store_bytes ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
  **  (store_sm3_ti )
  **  (UCharArray.undef_full result_pre 32 )
|--
  “ (aligned_4 result_pre ) ” 
  &&  “ (sm3_digest_input_aligned (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) ) ” 
  &&  “ (retval_8 = (( &( "total" ) ) + ((2 + id_len_pre ) * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength ((app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))))) = 192) ” 
  &&  “ (u8_list_bounded (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) ) ” 
  &&  “ (((2 + id_len_pre ) + 192 ) <= 250) ” 
  &&  “ (u8_list_bounded (rev (bytes_2)) ) ” 
  &&  “ ((Zlength ((rev (bytes_2)))) = 32) ” 
  &&  “ (retval_7 = (( &( "charlist" ) ) + (160 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_2)) = 32) ” 
  &&  “ (u8_list_bounded bytes_2 ) ” 
  &&  “ (u8_list_bounded (rev (bytes)) ) ” 
  &&  “ ((Zlength ((rev (bytes)))) = 32) ” 
  &&  “ (retval_6 = (( &( "charlist" ) ) + (128 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes)) = 32) ” 
  &&  “ (u8_list_bounded bytes ) ” 
  &&  “ (u8_list_bounded (rev (bytes_4)) ) ” 
  &&  “ ((Zlength ((rev (bytes_4)))) = 32) ” 
  &&  “ (retval_5 = (( &( "charlist" ) ) + (96 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_4)) = 32) ” 
  &&  “ (u8_list_bounded bytes_4 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_3)) ) ” 
  &&  “ ((Zlength ((rev (bytes_3)))) = 32) ” 
  &&  “ (retval_4 = (( &( "charlist" ) ) + (64 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_3)) = 32) ” 
  &&  “ (u8_list_bounded bytes_3 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_6)) ) ” 
  &&  “ ((Zlength ((rev (bytes_6)))) = 32) ” 
  &&  “ (retval_3 = (( &( "charlist" ) ) + (32 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_6)) = 32) ” 
  &&  “ (u8_list_bounded bytes_6 ) ” 
  &&  “ (u8_list_bounded (rev (bytes_5)) ) ” 
  &&  “ ((Zlength ((rev (bytes_5)))) = 32) ” 
  &&  “ (retval_2 = (( &( "charlist" ) ) + (0 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (bytes_5)) = 32) ” 
  &&  “ (u8_list_bounded bytes_5 ) ” 
  &&  “ (retval = (( &( "total" ) ) + (2 * sizeof(UCHAR)))) ” 
  &&  “ ((Zlength (ID)) = id_len_pre) ” 
  &&  “ (u8_list_bounded ID ) ” 
  &&  “ ((2 + id_len_pre ) <= 250) ” 
  &&  “ (aligned_4 ( &( "SM2_b" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_6)) = SM2_B_Z) ” 
  &&  “ (aligned_4 ( &( "SM2_a" ) ) ) ” 
  &&  “ ((u8_list_value (bytes_5)) = SM2_A_Z) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_4)) = y) ” 
  &&  “ (aligned_4 &(( &( "SM2_G" ) )->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes_3)) = x) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "y") ) ” 
  &&  “ ((u8_list_value (bytes_2)) = y_2) ” 
  &&  “ (aligned_4 &((pubkey_pre)  # "AFPoint" ->ₛ "x") ) ” 
  &&  “ ((u8_list_value (bytes)) = x_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ (SM2_A_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_A_Z) ” 
  &&  “ (SM2_B_Z < SM2_P_Z) ” 
  &&  “ (0 <= SM2_B_Z) ” 
  &&  “ (y = (sm2_point_y (SM2_G_POINT))) ” 
  &&  “ (x = (sm2_point_x (SM2_G_POINT))) ” 
  &&  “ (y_2 = (sm2_point_y (P))) ” 
  &&  “ (x_2 = (sm2_point_x (P))) ” 
  &&  “ (afpoint_represents x_2 y_2 P ) ” 
  &&  “ (afpoint_represents x y SM2_G_POINT ) ” 
  &&  “ (aligned_4 (( &( "total" ) ) + (0 * sizeof(UCHAR))) ) ” 
  &&  “ (id_len_pre <= 50) ” 
  &&  “ (sm2_id_digest_output_aligned result_pre id_len_pre ) ”
  &&  (store_bytes (( &( "total" ) ) + (0 * sizeof(UCHAR))) ((2 + id_len_pre ) + 192 ) (sm2_za_input (ID) (P)) )
  **  (UCharArray.undef_full result_pre 32 )
  **  (store_sm3_ti )
  **  (UCharArray.full ( &( "charlist" ) ) (0 + 192 ) (app ((u256_to_be_bytes (SM2_A_Z))) ((app ((u256_to_be_bytes (SM2_B_Z))) ((app ((u256_to_be_bytes ((sm2_point_x (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_y (SM2_G_POINT))))) ((app ((u256_to_be_bytes ((sm2_point_x (P))))) ((u256_to_be_bytes ((sm2_point_y (P)))))))))))))) )
  **  (UCharArray.undef_seg ( &( "total" ) ) ((2 + id_len_pre ) + 192 ) 250 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_u256 &((pubkey_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "x") x )
  **  (store_u256 &(( &( "SM2_G" ) )->ₛ "y") y )
  **  (store_u256 ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_u256 ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_bytes id_pre id_len_pre ID )
.

Definition sm2_get_id_digest_partial_solve_wit_18 := sm2_get_id_digest_partial_solve_wit_18_pure -> sm2_get_id_digest_partial_solve_wit_18_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include byte_memory_views_Strategy_Correct.
Include sm2_protocol_views_Strategy_Correct.
Include sm2_za_buffers_Strategy_Correct.

Axiom proof_of_sm2_get_id_digest_safety_wit_1 : sm2_get_id_digest_safety_wit_1.
Axiom proof_of_sm2_get_id_digest_safety_wit_2 : sm2_get_id_digest_safety_wit_2.
Axiom proof_of_sm2_get_id_digest_safety_wit_3 : sm2_get_id_digest_safety_wit_3.
Axiom proof_of_sm2_get_id_digest_safety_wit_4 : sm2_get_id_digest_safety_wit_4.
Axiom proof_of_sm2_get_id_digest_safety_wit_5 : sm2_get_id_digest_safety_wit_5.
Axiom proof_of_sm2_get_id_digest_safety_wit_6 : sm2_get_id_digest_safety_wit_6.
Axiom proof_of_sm2_get_id_digest_safety_wit_7 : sm2_get_id_digest_safety_wit_7.
Axiom proof_of_sm2_get_id_digest_safety_wit_8 : sm2_get_id_digest_safety_wit_8.
Axiom proof_of_sm2_get_id_digest_safety_wit_9 : sm2_get_id_digest_safety_wit_9.
Axiom proof_of_sm2_get_id_digest_safety_wit_10 : sm2_get_id_digest_safety_wit_10.
Axiom proof_of_sm2_get_id_digest_safety_wit_11 : sm2_get_id_digest_safety_wit_11.
Axiom proof_of_sm2_get_id_digest_safety_wit_12 : sm2_get_id_digest_safety_wit_12.
Axiom proof_of_sm2_get_id_digest_safety_wit_13 : sm2_get_id_digest_safety_wit_13.
Axiom proof_of_sm2_get_id_digest_safety_wit_14 : sm2_get_id_digest_safety_wit_14.
Axiom proof_of_sm2_get_id_digest_safety_wit_15 : sm2_get_id_digest_safety_wit_15.
Axiom proof_of_sm2_get_id_digest_safety_wit_16 : sm2_get_id_digest_safety_wit_16.
Axiom proof_of_sm2_get_id_digest_safety_wit_17 : sm2_get_id_digest_safety_wit_17.
Axiom proof_of_sm2_get_id_digest_safety_wit_18 : sm2_get_id_digest_safety_wit_18.
Axiom proof_of_sm2_get_id_digest_safety_wit_19 : sm2_get_id_digest_safety_wit_19.
Axiom proof_of_sm2_get_id_digest_safety_wit_20 : sm2_get_id_digest_safety_wit_20.
Axiom proof_of_sm2_get_id_digest_safety_wit_21 : sm2_get_id_digest_safety_wit_21.
Axiom proof_of_sm2_get_id_digest_safety_wit_22 : sm2_get_id_digest_safety_wit_22.
Axiom proof_of_sm2_get_id_digest_safety_wit_23 : sm2_get_id_digest_safety_wit_23.
Axiom proof_of_sm2_get_id_digest_safety_wit_24 : sm2_get_id_digest_safety_wit_24.
Axiom proof_of_sm2_get_id_digest_safety_wit_25 : sm2_get_id_digest_safety_wit_25.
Axiom proof_of_sm2_get_id_digest_safety_wit_26 : sm2_get_id_digest_safety_wit_26.
Axiom proof_of_sm2_get_id_digest_safety_wit_27 : sm2_get_id_digest_safety_wit_27.
Axiom proof_of_sm2_get_id_digest_safety_wit_28 : sm2_get_id_digest_safety_wit_28.
Axiom proof_of_sm2_get_id_digest_safety_wit_29 : sm2_get_id_digest_safety_wit_29.
Axiom proof_of_sm2_get_id_digest_safety_wit_30 : sm2_get_id_digest_safety_wit_30.
Axiom proof_of_sm2_get_id_digest_safety_wit_31 : sm2_get_id_digest_safety_wit_31.
Axiom proof_of_sm2_get_id_digest_safety_wit_32 : sm2_get_id_digest_safety_wit_32.
Axiom proof_of_sm2_get_id_digest_safety_wit_33 : sm2_get_id_digest_safety_wit_33.
Axiom proof_of_sm2_get_id_digest_safety_wit_34 : sm2_get_id_digest_safety_wit_34.
Axiom proof_of_sm2_get_id_digest_safety_wit_35 : sm2_get_id_digest_safety_wit_35.
Axiom proof_of_sm2_get_id_digest_safety_wit_36 : sm2_get_id_digest_safety_wit_36.
Axiom proof_of_sm2_get_id_digest_safety_wit_37 : sm2_get_id_digest_safety_wit_37.
Axiom proof_of_sm2_get_id_digest_safety_wit_38 : sm2_get_id_digest_safety_wit_38.
Axiom proof_of_sm2_get_id_digest_safety_wit_39 : sm2_get_id_digest_safety_wit_39.
Axiom proof_of_sm2_get_id_digest_safety_wit_40 : sm2_get_id_digest_safety_wit_40.
Axiom proof_of_sm2_get_id_digest_safety_wit_41 : sm2_get_id_digest_safety_wit_41.
Axiom proof_of_sm2_get_id_digest_safety_wit_42 : sm2_get_id_digest_safety_wit_42.
Axiom proof_of_sm2_get_id_digest_safety_wit_43 : sm2_get_id_digest_safety_wit_43.
Axiom proof_of_sm2_get_id_digest_safety_wit_44 : sm2_get_id_digest_safety_wit_44.
Axiom proof_of_sm2_get_id_digest_safety_wit_45 : sm2_get_id_digest_safety_wit_45.
Axiom proof_of_sm2_get_id_digest_safety_wit_46 : sm2_get_id_digest_safety_wit_46.
Axiom proof_of_sm2_get_id_digest_safety_wit_47 : sm2_get_id_digest_safety_wit_47.
Axiom proof_of_sm2_get_id_digest_safety_wit_48 : sm2_get_id_digest_safety_wit_48.
Axiom proof_of_sm2_get_id_digest_safety_wit_49 : sm2_get_id_digest_safety_wit_49.
Axiom proof_of_sm2_get_id_digest_safety_wit_50 : sm2_get_id_digest_safety_wit_50.
Axiom proof_of_sm2_get_id_digest_safety_wit_51 : sm2_get_id_digest_safety_wit_51.
Axiom proof_of_sm2_get_id_digest_safety_wit_52 : sm2_get_id_digest_safety_wit_52.
Axiom proof_of_sm2_get_id_digest_safety_wit_53 : sm2_get_id_digest_safety_wit_53.
Axiom proof_of_sm2_get_id_digest_safety_wit_54 : sm2_get_id_digest_safety_wit_54.
Axiom proof_of_sm2_get_id_digest_safety_wit_55 : sm2_get_id_digest_safety_wit_55.
Axiom proof_of_sm2_get_id_digest_safety_wit_56 : sm2_get_id_digest_safety_wit_56.
Axiom proof_of_sm2_get_id_digest_safety_wit_57 : sm2_get_id_digest_safety_wit_57.
Axiom proof_of_sm2_get_id_digest_safety_wit_58 : sm2_get_id_digest_safety_wit_58.
Axiom proof_of_sm2_get_id_digest_entail_wit_1 : sm2_get_id_digest_entail_wit_1.
Axiom proof_of_sm2_get_id_digest_entail_wit_2 : sm2_get_id_digest_entail_wit_2.
Axiom proof_of_sm2_get_id_digest_entail_wit_3 : sm2_get_id_digest_entail_wit_3.
Axiom proof_of_sm2_get_id_digest_entail_wit_4 : sm2_get_id_digest_entail_wit_4.
Axiom proof_of_sm2_get_id_digest_entail_wit_5 : sm2_get_id_digest_entail_wit_5.
Axiom proof_of_sm2_get_id_digest_entail_wit_6 : sm2_get_id_digest_entail_wit_6.
Axiom proof_of_sm2_get_id_digest_entail_wit_7 : sm2_get_id_digest_entail_wit_7.
Axiom proof_of_sm2_get_id_digest_entail_wit_8 : sm2_get_id_digest_entail_wit_8.
Axiom proof_of_sm2_get_id_digest_entail_wit_9 : sm2_get_id_digest_entail_wit_9.
Axiom proof_of_sm2_get_id_digest_entail_wit_10 : sm2_get_id_digest_entail_wit_10.
Axiom proof_of_sm2_get_id_digest_entail_wit_11 : sm2_get_id_digest_entail_wit_11.
Axiom proof_of_sm2_get_id_digest_entail_wit_12 : sm2_get_id_digest_entail_wit_12.
Axiom proof_of_sm2_get_id_digest_entail_wit_13 : sm2_get_id_digest_entail_wit_13.
Axiom proof_of_sm2_get_id_digest_entail_wit_14 : sm2_get_id_digest_entail_wit_14.
Axiom proof_of_sm2_get_id_digest_entail_wit_15 : sm2_get_id_digest_entail_wit_15.
Axiom proof_of_sm2_get_id_digest_entail_wit_16 : sm2_get_id_digest_entail_wit_16.
Axiom proof_of_sm2_get_id_digest_entail_wit_17 : sm2_get_id_digest_entail_wit_17.
Axiom proof_of_sm2_get_id_digest_entail_wit_18 : sm2_get_id_digest_entail_wit_18.
Axiom proof_of_sm2_get_id_digest_entail_wit_19 : sm2_get_id_digest_entail_wit_19.
Axiom proof_of_sm2_get_id_digest_entail_wit_20 : sm2_get_id_digest_entail_wit_20.
Axiom proof_of_sm2_get_id_digest_entail_wit_21 : sm2_get_id_digest_entail_wit_21.
Axiom proof_of_sm2_get_id_digest_entail_wit_22 : sm2_get_id_digest_entail_wit_22.
Axiom proof_of_sm2_get_id_digest_entail_wit_23 : sm2_get_id_digest_entail_wit_23.
Axiom proof_of_sm2_get_id_digest_entail_wit_24 : sm2_get_id_digest_entail_wit_24.
Axiom proof_of_sm2_get_id_digest_entail_wit_25 : sm2_get_id_digest_entail_wit_25.
Axiom proof_of_sm2_get_id_digest_entail_wit_26 : sm2_get_id_digest_entail_wit_26.
Axiom proof_of_sm2_get_id_digest_entail_wit_27 : sm2_get_id_digest_entail_wit_27.
Axiom proof_of_sm2_get_id_digest_entail_wit_28 : sm2_get_id_digest_entail_wit_28.
Axiom proof_of_sm2_get_id_digest_return_wit_1 : sm2_get_id_digest_return_wit_1.
Axiom proof_of_sm2_get_id_digest_return_wit_2 : sm2_get_id_digest_return_wit_2.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_1 : sm2_get_id_digest_partial_solve_wit_1.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_2 : sm2_get_id_digest_partial_solve_wit_2.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_3 : sm2_get_id_digest_partial_solve_wit_3.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_4_pure : sm2_get_id_digest_partial_solve_wit_4_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_4 : sm2_get_id_digest_partial_solve_wit_4.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_5_pure : sm2_get_id_digest_partial_solve_wit_5_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_5 : sm2_get_id_digest_partial_solve_wit_5.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_6_pure : sm2_get_id_digest_partial_solve_wit_6_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_6 : sm2_get_id_digest_partial_solve_wit_6.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_7_pure : sm2_get_id_digest_partial_solve_wit_7_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_7 : sm2_get_id_digest_partial_solve_wit_7.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_8_pure : sm2_get_id_digest_partial_solve_wit_8_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_8 : sm2_get_id_digest_partial_solve_wit_8.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_9_pure : sm2_get_id_digest_partial_solve_wit_9_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_9 : sm2_get_id_digest_partial_solve_wit_9.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_10_pure : sm2_get_id_digest_partial_solve_wit_10_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_10 : sm2_get_id_digest_partial_solve_wit_10.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_11_pure : sm2_get_id_digest_partial_solve_wit_11_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_11 : sm2_get_id_digest_partial_solve_wit_11.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_12_pure : sm2_get_id_digest_partial_solve_wit_12_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_12 : sm2_get_id_digest_partial_solve_wit_12.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_13_pure : sm2_get_id_digest_partial_solve_wit_13_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_13 : sm2_get_id_digest_partial_solve_wit_13.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_14_pure : sm2_get_id_digest_partial_solve_wit_14_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_14 : sm2_get_id_digest_partial_solve_wit_14.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_15_pure : sm2_get_id_digest_partial_solve_wit_15_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_15 : sm2_get_id_digest_partial_solve_wit_15.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_16_pure : sm2_get_id_digest_partial_solve_wit_16_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_16 : sm2_get_id_digest_partial_solve_wit_16.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_17_pure : sm2_get_id_digest_partial_solve_wit_17_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_17 : sm2_get_id_digest_partial_solve_wit_17.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_18_pure : sm2_get_id_digest_partial_solve_wit_18_pure.
Axiom proof_of_sm2_get_id_digest_partial_solve_wit_18 : sm2_get_id_digest_partial_solve_wit_18.

End VC_Correct.
