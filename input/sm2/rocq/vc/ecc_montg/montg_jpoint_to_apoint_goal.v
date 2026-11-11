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
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.

(*----- Function montg_jpoint_to_apoint -----*)

Definition montg_jpoint_to_apoint_safety_wit_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Z_x_only <> 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_3 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) (PreH6 : (rx_pre = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_4 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) (PreH6 : (rx_pre <> 0)) (PreH7 : (ry_pre <> 0)) ,
  (store_u256_limbs rx_pre 0 )
  **  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_5 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) (PreH6 : (rx_pre <> 0)) (PreH7 : (ry_pre = 0)) ,
  (store_u256_limbs rx_pre 0 )
  **  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_jpoint_to_apoint_safety_wit_6 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint_safety_wit_7 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_8 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_9 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre = 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_10 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) (PreH18 : (ry_pre <> 0)) ,
  (store_u256_limbs rx_pre X_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_11 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) (PreH18 : (ry_pre = 0)) ,
  (store_u256_limbs rx_pre X_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_jpoint_to_apoint_safety_wit_12 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint_safety_wit_13 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint_safety_wit_14 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_15 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : (rx_pre = rx_pre)) (PreH2 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH3 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH4 : (0 <= ZI)) (PreH5 : (ZI < SM2_P_Z)) (PreH6 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH7 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH8 : (retval_2 = 0)) (PreH9 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH10 : (Z_x_only < SM2_P_Z)) (PreH11 : (0 <= Z_x_only)) (PreH12 : (Y_x_only < SM2_P_Z)) (PreH13 : (0 <= Y_x_only)) (PreH14 : (X_x_only < SM2_P_Z)) (PreH15 : (0 <= X_x_only)) (PreH16 : (Z_x_only <> 0)) (PreH17 : (retval = 0)) (PreH18 : (Z_x_only <> 0)) (PreH19 : (rx_pre <> 0)) (PreH20 : (ry_pre = 0)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (rx_pre <> 0)) (PreH24 : (ry_pre <> 0)) ,
  (store_u256_limbs rx_pre (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ False ”
.

Definition montg_jpoint_to_apoint_safety_wit_16 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : (rx_pre = rx_pre)) (PreH2 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH3 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH4 : (0 <= ZI)) (PreH5 : (ZI < SM2_P_Z)) (PreH6 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH7 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH8 : (retval_2 = 0)) (PreH9 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH10 : (Z_x_only < SM2_P_Z)) (PreH11 : (0 <= Z_x_only)) (PreH12 : (Y_x_only < SM2_P_Z)) (PreH13 : (0 <= Y_x_only)) (PreH14 : (X_x_only < SM2_P_Z)) (PreH15 : (0 <= X_x_only)) (PreH16 : (Z_x_only <> 0)) (PreH17 : (retval = 0)) (PreH18 : (Z_x_only <> 0)) (PreH19 : (rx_pre <> 0)) (PreH20 : (ry_pre = 0)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (rx_pre <> 0)) (PreH24 : (ry_pre = 0)) ,
  (store_u256_limbs rx_pre (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_jpoint_to_apoint_entail_wit_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (PreH1 : (rx_pre <> 0)) (PreH2 : (ry_pre = 0)) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_2_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Z_x_only <> 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_2_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval_2 = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_3_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (Z_x_only <> 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval_2 <> 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (Z_x_only = 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_3_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 1) ” 
  &&  “ (Z_x_only = 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_4 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Z_x_only <> 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_5 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only <> 0)) (PreH2 : (retval = 0)) (PreH3 : (Z_x_only <> 0)) (PreH4 : (rx_pre <> 0)) (PreH5 : (ry_pre = 0)) (PreH6 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (X_x_only)) (mont_p (Y_x_only)) (mont_p (Z_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_6 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_x_only)) (mont_p (Y_x_only)) (mont_p (Z_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_7_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_3: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_3 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval_2: Z) ,
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_7_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_8_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_x_only)) = MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_8_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_3: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_3 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval_2: Z) ,
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_x_only)) = MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_9 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_x_only)) = MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UndefStructPredu32 rx_pre )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_10 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp rx_pre X_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_x_only)) = MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (store_u256_limbs rx_pre X_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
.

Definition montg_jpoint_to_apoint_entail_wit_11 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_entail_wit_12 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
.

Definition montg_jpoint_to_apoint_entail_wit_13 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
.

Definition montg_jpoint_to_apoint_entail_wit_14 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : (rx_pre = rx_pre)) (PreH2 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH3 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH4 : (0 <= ZI)) (PreH5 : (ZI < SM2_P_Z)) (PreH6 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH7 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH8 : (retval_2 = 0)) (PreH9 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH10 : (Z_x_only < SM2_P_Z)) (PreH11 : (0 <= Z_x_only)) (PreH12 : (Y_x_only < SM2_P_Z)) (PreH13 : (0 <= Y_x_only)) (PreH14 : (X_x_only < SM2_P_Z)) (PreH15 : (0 <= X_x_only)) (PreH16 : (Z_x_only <> 0)) (PreH17 : (retval = 0)) (PreH18 : (Z_x_only <> 0)) (PreH19 : (rx_pre <> 0)) (PreH20 : (ry_pre = 0)) (PreH21 : (retval = 0)) (PreH22 : (retval_2 = 0)) (PreH23 : (rx_pre <> 0)) ,
  (store_fp rx_pre (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (rx_pre = rx_pre) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (store_u256_limbs rx_pre (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
.

Definition montg_jpoint_to_apoint_return_wit_1 := 
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI_2: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI_2)) (PreH4 : (ZI_2 < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI_2 )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) (PreH23 : (ry_pre = 0)) ,
  (store_u256_limbs rx_pre (Zmod (((X_x_only * ZI_2 ) * ZI_2 )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
|--
  EX (RX: Z)  (ZI: Z) ,
  “ (1 = 1) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ (RX = (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_u256_limbs rx_pre RX )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI_2: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI_2)) (PreH4 : (ZI_2 < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI_2 )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) (PreH23 : (ry_pre = 0)) ,
  TT && emp 
|--
  EX (ZI: Z) ,
  “ ((Zmod (((X_x_only * ZI_2 ) * ZI_2 )) (SM2_P_Z)) = (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ”
  &&  emp
).

Definition montg_jpoint_to_apoint_return_wit_2 := 
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) (PreH18 : (ry_pre = 0)) ,
  (store_u256_limbs rx_pre X_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
|--
  EX (RX: Z)  (ZI: Z) ,
  “ (1 = 1) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ (RX = (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_u256_limbs rx_pre RX )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) (PreH18 : (ry_pre = 0)) ,
  TT && emp 
|--
  EX (ZI: Z) ,
  “ (X_x_only = (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ”
  &&  emp
).

Definition montg_jpoint_to_apoint_return_wit_3 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) (PreH6 : (rx_pre <> 0)) (PreH7 : (ry_pre = 0)) ,
  (store_u256_limbs rx_pre 0 )
  **  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (Z_x_only = 0) ” 
  &&  “ (RX = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_u256_limbs rx_pre RX )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (PreH1 : (rx_pre <> 0)) (PreH2 : (ry_pre = 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_x_only = 0)) (PreH3 : (rx_pre <> 0)) (PreH4 : (ry_pre = 0)) (PreH5 : (retval <> 0)) (PreH6 : (rx_pre <> 0)) ,
  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 1) ” 
  &&  “ (Z_x_only = 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (UInt64Array.undef_full rx_pre 4 )
  **  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_3_pure := 
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Z_x_only)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_x_only))) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ”
) \/
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (0 <= (mont_p (Z_x_only))) ” 
  &&  “ ((mont_p (Z_x_only)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (mont_p (Z_x_only))) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_3_pure_split_goal_3 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Z_x_only)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_3_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (PreH1 : (Z_x_only < SM2_P_Z)) (PreH2 : (0 <= Z_x_only)) (PreH3 : (Y_x_only < SM2_P_Z)) (PreH4 : (0 <= Y_x_only)) (PreH5 : (X_x_only < SM2_P_Z)) (PreH6 : (0 <= X_x_only)) (PreH7 : (Z_x_only <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_x_only <> 0)) (PreH10 : (rx_pre <> 0)) (PreH11 : (ry_pre = 0)) (PreH12 : (retval = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Z_x_only)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_x_only))) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_3 := montg_jpoint_to_apoint_partial_solve_wit_3_pure -> montg_jpoint_to_apoint_partial_solve_wit_3_aux.

Definition montg_jpoint_to_apoint_partial_solve_wit_4_pure := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= X_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_4_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_x_only)) = MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) (PreH17 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= X_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_x_only)) = MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (UInt64Array.undef_full &((rx_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_4 := montg_jpoint_to_apoint_partial_solve_wit_4_pure -> montg_jpoint_to_apoint_partial_solve_wit_4_aux.

Definition montg_jpoint_to_apoint_partial_solve_wit_5_pure := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= Z_x_only) ” 
  &&  “ (Z_x_only < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_5_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= Z_x_only) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_5 := montg_jpoint_to_apoint_partial_solve_wit_5_pure -> montg_jpoint_to_apoint_partial_solve_wit_5_aux.

Definition montg_jpoint_to_apoint_partial_solve_wit_6_pure := 
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ (0 <= Z_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ”
) \/
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ”
).

Definition montg_jpoint_to_apoint_partial_solve_wit_6_pure_split_goal_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_6_pure_split_goal_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_6_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH4 : (Z_x_only < SM2_P_Z)) (PreH5 : (0 <= Z_x_only)) (PreH6 : (Y_x_only < SM2_P_Z)) (PreH7 : (0 <= Y_x_only)) (PreH8 : (X_x_only < SM2_P_Z)) (PreH9 : (0 <= X_x_only)) (PreH10 : (Z_x_only <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_x_only <> 0)) (PreH13 : (rx_pre <> 0)) (PreH14 : (ry_pre = 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ (0 <= Z_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "T" ) ) Z_x_only )
  **  (UInt64Array.undef_full (&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_6 := montg_jpoint_to_apoint_partial_solve_wit_6_pure -> montg_jpoint_to_apoint_partial_solve_wit_6_aux.

Definition montg_jpoint_to_apoint_partial_solve_wit_7_pure := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) ,
  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_7_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) ,
  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full rx_pre 4 )
|--
  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (UInt64Array.undef_full &(( &( "Zisqr" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full rx_pre 4 )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_7 := montg_jpoint_to_apoint_partial_solve_wit_7_pure -> montg_jpoint_to_apoint_partial_solve_wit_7_aux.

Definition montg_jpoint_to_apoint_partial_solve_wit_8_pure := 
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (0 <= X_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ”
) \/
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_8_pure_split_goal_3 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_8_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (UndefStructPredu32 rx_pre )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_bn_zero )
|--
  “ (0 <= X_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (UInt64Array.undef_full &((rx_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_8 := montg_jpoint_to_apoint_partial_solve_wit_8_pure -> montg_jpoint_to_apoint_partial_solve_wit_8_aux.

Definition montg_jpoint_to_apoint_partial_solve_wit_9_pure := 
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp rx_pre (mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (rx_pre = rx_pre) ” 
  &&  “ ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) = (mont_p ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))))) ”
) \/
(
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp rx_pre (mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) = (mont_p ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))))) ” 
  &&  “ (0 <= (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_1 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp rx_pre (mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) = (mont_p ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))))) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_2 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp rx_pre (mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ (0 <= (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_9_pure_split_goal_3 := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp rx_pre (mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "rx" ) )) # Ptr  |-> rx_pre)
  **  ((( &( "ry" ) )) # Ptr  |-> ry_pre)
|--
  “ ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint_partial_solve_wit_9_aux := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (Z_x_only: Z) (Y_x_only: Z) (X_x_only: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_x_only)) <> MONTG_ONE_Z)) (PreH9 : (Z_x_only < SM2_P_Z)) (PreH10 : (0 <= Z_x_only)) (PreH11 : (Y_x_only < SM2_P_Z)) (PreH12 : (0 <= Y_x_only)) (PreH13 : (X_x_only < SM2_P_Z)) (PreH14 : (0 <= X_x_only)) (PreH15 : (Z_x_only <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_x_only <> 0)) (PreH18 : (rx_pre <> 0)) (PreH19 : (ry_pre = 0)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) (PreH22 : (rx_pre <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp rx_pre (mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
|--
  “ (rx_pre = rx_pre) ” 
  &&  “ ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p ((X_x_only * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) = (mont_p ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))))) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_x_only)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Z_x_only) ” 
  &&  “ (Y_x_only < SM2_P_Z) ” 
  &&  “ (0 <= Y_x_only) ” 
  &&  “ (X_x_only < SM2_P_Z) ” 
  &&  “ (0 <= X_x_only) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (rx_pre <> 0) ”
  &&  (store_fp rx_pre (mont_p ((Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z)))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_x_only)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_x_only )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_x_only)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_x_only)) )
  **  (store_bn_zero )
.

Definition montg_jpoint_to_apoint_partial_solve_wit_9 := montg_jpoint_to_apoint_partial_solve_wit_9_pure -> montg_jpoint_to_apoint_partial_solve_wit_9_aux.

Definition montg_jpoint_to_apoint_derive_point_x_only_by_x_only := 
forall (ry_pre: Z) (rx_pre: Z) (a_pre: Z) (P_point_x_only: ec_point) ,
  “ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ”
  &&  (store_mont_jpoint a_pre P_point_x_only )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (X_x_only: Z) (Y_x_only: Z) (Z_x_only: Z) ,
  (“ (rx_pre <> 0) ” 
  &&  “ (ry_pre = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (UInt64Array.undef_full rx_pre 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  (((EX RX_2 retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (Z_x_only = 0) ” 
  &&  “ (RX_2 = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_u256_limbs rx_pre RX_2 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX RX_2 ZI retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (Z_x_only <> 0) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_x_only * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ (RX_2 = (Zmod (((X_x_only * ZI ) * ZI )) (SM2_P_Z))) ”
  &&  (store_mont_jpoint_coords a_pre X_x_only Y_x_only Z_x_only )
  **  (store_u256_limbs rx_pre RX_2 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
  -*
  (EX RX RY retval,
  “ (retval = 1) ” 
  &&  “ (ry_pre = 0) ” 
  &&  “ (afpoint_represents RX RY P_point_x_only ) ”
  &&  (store_mont_jpoint a_pre P_point_x_only )
  **  (store_u256_limbs rx_pre RX )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include u32_alias_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.

Axiom proof_of_montg_jpoint_to_apoint_safety_wit_1 : montg_jpoint_to_apoint_safety_wit_1.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_2 : montg_jpoint_to_apoint_safety_wit_2.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_3 : montg_jpoint_to_apoint_safety_wit_3.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_4 : montg_jpoint_to_apoint_safety_wit_4.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_5 : montg_jpoint_to_apoint_safety_wit_5.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_6 : montg_jpoint_to_apoint_safety_wit_6.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_7 : montg_jpoint_to_apoint_safety_wit_7.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_8 : montg_jpoint_to_apoint_safety_wit_8.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_9 : montg_jpoint_to_apoint_safety_wit_9.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_10 : montg_jpoint_to_apoint_safety_wit_10.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_11 : montg_jpoint_to_apoint_safety_wit_11.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_12 : montg_jpoint_to_apoint_safety_wit_12.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_13 : montg_jpoint_to_apoint_safety_wit_13.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_14 : montg_jpoint_to_apoint_safety_wit_14.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_15 : montg_jpoint_to_apoint_safety_wit_15.
Axiom proof_of_montg_jpoint_to_apoint_safety_wit_16 : montg_jpoint_to_apoint_safety_wit_16.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_1 : montg_jpoint_to_apoint_entail_wit_1.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_2_1 : montg_jpoint_to_apoint_entail_wit_2_1.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_2_2 : montg_jpoint_to_apoint_entail_wit_2_2.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_3_1 : montg_jpoint_to_apoint_entail_wit_3_1.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_3_2 : montg_jpoint_to_apoint_entail_wit_3_2.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_4 : montg_jpoint_to_apoint_entail_wit_4.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_5 : montg_jpoint_to_apoint_entail_wit_5.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_6 : montg_jpoint_to_apoint_entail_wit_6.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_7_1 : montg_jpoint_to_apoint_entail_wit_7_1.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_7_2 : montg_jpoint_to_apoint_entail_wit_7_2.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_8_1 : montg_jpoint_to_apoint_entail_wit_8_1.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_8_2 : montg_jpoint_to_apoint_entail_wit_8_2.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_9 : montg_jpoint_to_apoint_entail_wit_9.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_10 : montg_jpoint_to_apoint_entail_wit_10.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_11 : montg_jpoint_to_apoint_entail_wit_11.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_12 : montg_jpoint_to_apoint_entail_wit_12.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_13 : montg_jpoint_to_apoint_entail_wit_13.
Axiom proof_of_montg_jpoint_to_apoint_entail_wit_14 : montg_jpoint_to_apoint_entail_wit_14.
Axiom proof_of_montg_jpoint_to_apoint_return_wit_1 : montg_jpoint_to_apoint_return_wit_1.
Axiom proof_of_montg_jpoint_to_apoint_return_wit_2 : montg_jpoint_to_apoint_return_wit_2.
Axiom proof_of_montg_jpoint_to_apoint_return_wit_3 : montg_jpoint_to_apoint_return_wit_3.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_1 : montg_jpoint_to_apoint_partial_solve_wit_1.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_2 : montg_jpoint_to_apoint_partial_solve_wit_2.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_3_pure : montg_jpoint_to_apoint_partial_solve_wit_3_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_3 : montg_jpoint_to_apoint_partial_solve_wit_3.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_4_pure : montg_jpoint_to_apoint_partial_solve_wit_4_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_4 : montg_jpoint_to_apoint_partial_solve_wit_4.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_5_pure : montg_jpoint_to_apoint_partial_solve_wit_5_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_5 : montg_jpoint_to_apoint_partial_solve_wit_5.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_6_pure : montg_jpoint_to_apoint_partial_solve_wit_6_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_6 : montg_jpoint_to_apoint_partial_solve_wit_6.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_7_pure : montg_jpoint_to_apoint_partial_solve_wit_7_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_7 : montg_jpoint_to_apoint_partial_solve_wit_7.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_8_pure : montg_jpoint_to_apoint_partial_solve_wit_8_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_8 : montg_jpoint_to_apoint_partial_solve_wit_8.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_9_pure : montg_jpoint_to_apoint_partial_solve_wit_9_pure.
Axiom proof_of_montg_jpoint_to_apoint_partial_solve_wit_9 : montg_jpoint_to_apoint_partial_solve_wit_9.
Axiom proof_of_montg_jpoint_to_apoint_derive_point_x_only_by_x_only : montg_jpoint_to_apoint_derive_point_x_only_by_x_only.

End VC_Correct.
