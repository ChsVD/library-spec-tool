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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.

(*----- Function equ_to_JPoint_one -----*)

Definition equ_to_JPoint_one_safety_wit_1 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (JY_base = 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (JX_base <> 1)) (PreH10 : (JZ_base < SM2_P_Z)) (PreH11 : (0 <= JZ_base)) (PreH12 : (JY_base < SM2_P_Z)) (PreH13 : (0 <= JY_base)) (PreH14 : (JX_base < SM2_P_Z)) (PreH15 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ False ”
.

Definition equ_to_JPoint_one_safety_wit_2 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (JY_base <> 1)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (JX_base <> 1)) (PreH10 : (JZ_base < SM2_P_Z)) (PreH11 : (0 <= JZ_base)) (PreH12 : (JY_base < SM2_P_Z)) (PreH13 : (0 <= JY_base)) (PreH14 : (JX_base < SM2_P_Z)) (PreH15 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ False ”
.

Definition equ_to_JPoint_one_safety_wit_3 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (JZ_base = 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : (JY_base <> 1)) (PreH10 : (retval <> 0)) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1)) (PreH13 : (retval = 1)) (PreH14 : (JX_base = 1)) (PreH15 : (JZ_base < SM2_P_Z)) (PreH16 : (0 <= JZ_base)) (PreH17 : (JY_base < SM2_P_Z)) (PreH18 : (0 <= JY_base)) (PreH19 : (JX_base < SM2_P_Z)) (PreH20 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ False ”
.

Definition equ_to_JPoint_one_safety_wit_4 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (JZ_base <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : (JY_base <> 1)) (PreH10 : (retval <> 0)) (PreH11 : (0 <= retval)) (PreH12 : (retval <= 1)) (PreH13 : (retval = 1)) (PreH14 : (JX_base = 1)) (PreH15 : (JZ_base < SM2_P_Z)) (PreH16 : (0 <= JZ_base)) (PreH17 : (JY_base < SM2_P_Z)) (PreH18 : (0 <= JY_base)) (PreH19 : (JX_base < SM2_P_Z)) (PreH20 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ False ”
.

Definition equ_to_JPoint_one_return_wit_1 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (JZ_base = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (JY_base = 1)) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (JX_base = 1)) (PreH16 : (JZ_base < SM2_P_Z)) (PreH17 : (0 <= JZ_base)) (PreH18 : (JY_base < SM2_P_Z)) (PreH19 : (0 <= JY_base)) (PreH20 : (JX_base < SM2_P_Z)) (PreH21 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (JZ_base = 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JX_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
.

Definition equ_to_JPoint_one_return_wit_2 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 1)) (PreH5 : (JZ_base = 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (JY_base = 1)) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (JX_base = 1)) (PreH16 : (JZ_base < SM2_P_Z)) (PreH17 : (0 <= JZ_base)) (PreH18 : (JY_base < SM2_P_Z)) (PreH19 : (0 <= JY_base)) (PreH20 : (JX_base < SM2_P_Z)) (PreH21 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (JZ_base = 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base )
.

Definition equ_to_JPoint_one_return_wit_3 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 0)) (PreH5 : (JZ_base <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (JY_base = 1)) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (JX_base = 1)) (PreH16 : (JZ_base < SM2_P_Z)) (PreH17 : (0 <= JZ_base)) (PreH18 : (JY_base < SM2_P_Z)) (PreH19 : (0 <= JY_base)) (PreH20 : (JX_base < SM2_P_Z)) (PreH21 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base )
.

Definition equ_to_JPoint_one_return_wit_4 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 1)) (PreH4 : (retval_3 = 0)) (PreH5 : (JZ_base <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 1)) (PreH10 : (JY_base = 1)) (PreH11 : (retval <> 0)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 1)) (PreH15 : (JX_base = 1)) (PreH16 : (JZ_base < SM2_P_Z)) (PreH17 : (0 <= JZ_base)) (PreH18 : (JY_base < SM2_P_Z)) (PreH19 : (0 <= JY_base)) (PreH20 : (JX_base < SM2_P_Z)) (PreH21 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
|--
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (JZ_base = 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ (JX_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
.

Definition equ_to_JPoint_one_return_wit_5 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (JX_base <> 1)) (PreH6 : (JZ_base < SM2_P_Z)) (PreH7 : (0 <= JZ_base)) (PreH8 : (JY_base < SM2_P_Z)) (PreH9 : (0 <= JY_base)) (PreH10 : (JX_base < SM2_P_Z)) (PreH11 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JX_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
.

Definition equ_to_JPoint_one_return_wit_6 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (JX_base = 1)) (PreH6 : (JZ_base < SM2_P_Z)) (PreH7 : (0 <= JZ_base)) (PreH8 : (JY_base < SM2_P_Z)) (PreH9 : (0 <= JY_base)) (PreH10 : (JX_base < SM2_P_Z)) (PreH11 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (JZ_base = 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JX_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
.

Definition equ_to_JPoint_one_return_wit_7 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (JY_base <> 1)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (JX_base = 1)) (PreH11 : (JZ_base < SM2_P_Z)) (PreH12 : (0 <= JZ_base)) (PreH13 : (JY_base < SM2_P_Z)) (PreH14 : (0 <= JY_base)) (PreH15 : (JX_base < SM2_P_Z)) (PreH16 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
.

Definition equ_to_JPoint_one_return_wit_8 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (JY_base = 1)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (JX_base = 1)) (PreH11 : (JZ_base < SM2_P_Z)) (PreH12 : (0 <= JZ_base)) (PreH13 : (JY_base < SM2_P_Z)) (PreH14 : (0 <= JY_base)) (PreH15 : (JX_base < SM2_P_Z)) (PreH16 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (JZ_base = 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (JX_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
.

Definition equ_to_JPoint_one_partial_solve_wit_1 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) ,
  (store_jpoint_fields point_pre JX_base JY_base JZ_base )
|--
  “ (JZ_base < SM2_P_Z) ” 
  &&  “ (0 <= JZ_base) ” 
  &&  “ (JY_base < SM2_P_Z) ” 
  &&  “ (0 <= JY_base) ” 
  &&  “ (JX_base < SM2_P_Z) ” 
  &&  “ (0 <= JX_base) ”
  &&  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
.

Definition equ_to_JPoint_one_partial_solve_wit_2 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (JX_base <> 1)) (PreH6 : (JZ_base < SM2_P_Z)) (PreH7 : (0 <= JZ_base)) (PreH8 : (JY_base < SM2_P_Z)) (PreH9 : (0 <= JY_base)) (PreH10 : (JX_base < SM2_P_Z)) (PreH11 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (JX_base <> 1) ” 
  &&  “ (JZ_base < SM2_P_Z) ” 
  &&  “ (0 <= JZ_base) ” 
  &&  “ (JY_base < SM2_P_Z) ” 
  &&  “ (0 <= JY_base) ” 
  &&  “ (JX_base < SM2_P_Z) ” 
  &&  “ (0 <= JX_base) ”
  &&  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
.

Definition equ_to_JPoint_one_partial_solve_wit_3 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (JX_base = 1)) (PreH6 : (JZ_base < SM2_P_Z)) (PreH7 : (0 <= JZ_base)) (PreH8 : (JY_base < SM2_P_Z)) (PreH9 : (0 <= JY_base)) (PreH10 : (JX_base < SM2_P_Z)) (PreH11 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JZ_base < SM2_P_Z) ” 
  &&  “ (0 <= JZ_base) ” 
  &&  “ (JY_base < SM2_P_Z) ” 
  &&  “ (0 <= JY_base) ” 
  &&  “ (JX_base < SM2_P_Z) ” 
  &&  “ (0 <= JX_base) ”
  &&  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
.

Definition equ_to_JPoint_one_partial_solve_wit_4 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (JY_base = 1)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (JX_base = 1)) (PreH11 : (JZ_base < SM2_P_Z)) (PreH12 : (0 <= JZ_base)) (PreH13 : (JY_base < SM2_P_Z)) (PreH14 : (0 <= JY_base)) (PreH15 : (JX_base < SM2_P_Z)) (PreH16 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JZ_base < SM2_P_Z) ” 
  &&  “ (0 <= JZ_base) ” 
  &&  “ (JY_base < SM2_P_Z) ” 
  &&  “ (0 <= JY_base) ” 
  &&  “ (JX_base < SM2_P_Z) ” 
  &&  “ (0 <= JX_base) ”
  &&  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
.

Definition equ_to_JPoint_one_partial_solve_wit_5 := 
forall (point_pre: Z) (JZ_base: Z) (JY_base: Z) (JX_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (JY_base <> 1)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (JX_base = 1)) (PreH11 : (JZ_base < SM2_P_Z)) (PreH12 : (0 <= JZ_base)) (PreH13 : (JY_base < SM2_P_Z)) (PreH14 : (0 <= JY_base)) (PreH15 : (JX_base < SM2_P_Z)) (PreH16 : (0 <= JX_base)) ,
  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JY_base <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JZ_base < SM2_P_Z) ” 
  &&  “ (0 <= JZ_base) ” 
  &&  “ (JY_base < SM2_P_Z) ” 
  &&  “ (0 <= JY_base) ” 
  &&  “ (JX_base < SM2_P_Z) ” 
  &&  “ (0 <= JX_base) ”
  &&  (store_u256 &((point_pre)  # "JPoint" ->ₛ "z") JZ_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "y") JY_base )
  **  (store_u256 &((point_pre)  # "JPoint" ->ₛ "x") JX_base )
.

Definition equ_to_JPoint_one_derive_point_by_base := 
forall (point_pre: Z) (P_point: ec_point) ,
  (store_jpoint_with_canonical_infinity point_pre P_point )
|--
EX (JX_base: Z) (JY_base: Z) (JZ_base: Z) ,
  ((store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  **
  (((EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (JX_base = 1) ” 
  &&  “ (JY_base = 1) ” 
  &&  “ (JZ_base = 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JZ_base <> 0) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JY_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (JX_base <> 1) ”
  &&  (store_jpoint_fields point_pre JX_base JY_base JZ_base )))
  -*
  ((EX retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_point = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point_pre P_point ))
  ||
  (EX retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_point <> ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point_pre P_point ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include ecc_representation_Strategy_Correct.

Axiom proof_of_equ_to_JPoint_one_safety_wit_1 : equ_to_JPoint_one_safety_wit_1.
Axiom proof_of_equ_to_JPoint_one_safety_wit_2 : equ_to_JPoint_one_safety_wit_2.
Axiom proof_of_equ_to_JPoint_one_safety_wit_3 : equ_to_JPoint_one_safety_wit_3.
Axiom proof_of_equ_to_JPoint_one_safety_wit_4 : equ_to_JPoint_one_safety_wit_4.
Axiom proof_of_equ_to_JPoint_one_return_wit_1 : equ_to_JPoint_one_return_wit_1.
Axiom proof_of_equ_to_JPoint_one_return_wit_2 : equ_to_JPoint_one_return_wit_2.
Axiom proof_of_equ_to_JPoint_one_return_wit_3 : equ_to_JPoint_one_return_wit_3.
Axiom proof_of_equ_to_JPoint_one_return_wit_4 : equ_to_JPoint_one_return_wit_4.
Axiom proof_of_equ_to_JPoint_one_return_wit_5 : equ_to_JPoint_one_return_wit_5.
Axiom proof_of_equ_to_JPoint_one_return_wit_6 : equ_to_JPoint_one_return_wit_6.
Axiom proof_of_equ_to_JPoint_one_return_wit_7 : equ_to_JPoint_one_return_wit_7.
Axiom proof_of_equ_to_JPoint_one_return_wit_8 : equ_to_JPoint_one_return_wit_8.
Axiom proof_of_equ_to_JPoint_one_partial_solve_wit_1 : equ_to_JPoint_one_partial_solve_wit_1.
Axiom proof_of_equ_to_JPoint_one_partial_solve_wit_2 : equ_to_JPoint_one_partial_solve_wit_2.
Axiom proof_of_equ_to_JPoint_one_partial_solve_wit_3 : equ_to_JPoint_one_partial_solve_wit_3.
Axiom proof_of_equ_to_JPoint_one_partial_solve_wit_4 : equ_to_JPoint_one_partial_solve_wit_4.
Axiom proof_of_equ_to_JPoint_one_partial_solve_wit_5 : equ_to_JPoint_one_partial_solve_wit_5.
Axiom proof_of_equ_to_JPoint_one_derive_point_by_base : equ_to_JPoint_one_derive_point_by_base.

End VC_Correct.
