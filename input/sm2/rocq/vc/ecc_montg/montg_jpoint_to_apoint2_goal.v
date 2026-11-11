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

(*----- Function montg_jpoint_to_apoint2 -----*)

Definition montg_jpoint_to_apoint2_safety_wit_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint2_safety_wit_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Z_non_alias <> 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint2_safety_wit_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_4 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH2 : (retval = 1)) (PreH3 : (Z_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_5 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "y") 0 )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_6 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_7 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint2_safety_wit_8 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition montg_jpoint_to_apoint2_safety_wit_9 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_10 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_11 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_12 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_13 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH4 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH5 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH6 : (retval_2 = 1)) (PreH7 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH8 : (Z_non_alias < SM2_P_Z)) (PreH9 : (0 <= Z_non_alias)) (PreH10 : (Y_non_alias < SM2_P_Z)) (PreH11 : (0 <= Y_non_alias)) (PreH12 : (X_non_alias < SM2_P_Z)) (PreH13 : (0 <= X_non_alias)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (Z_non_alias <> 0)) (PreH17 : (retval = 0)) (PreH18 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_14 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_15 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_jpoint_to_apoint2_safety_wit_16 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)))) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "y") (mont_p ((Y_non_alias * (Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_jpoint_to_apoint2_entail_wit_1_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Z_non_alias <> 0)) (PreH3 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_1_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval_2 = 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_2_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (Z_non_alias <> 0)) (PreH3 : (retval_2 <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (Z_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_2_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (retval = 1) ” 
  &&  “ (Z_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Z_non_alias <> 0)) (PreH3 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_4 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias <> 0)) (PreH2 : (retval = 0)) (PreH3 : (Z_non_alias <> 0)) (PreH4 : (retval = 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_5_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_3 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_3 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval_2: Z) ,
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_5_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_6_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_non_alias)) = MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_6_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_3 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_3 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval_2: Z) ,
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_non_alias)) = MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_entail_wit_7 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_jpoint_to_apoint2_return_wit_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI_2: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI_2)) (PreH4 : (ZI_2 < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI_2 )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "y") (mont_p ((Y_non_alias * (Zmod (((ZI_2 * ZI_2 ) * ZI_2 )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI_2 * ZI_2 )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_bn_zero )
|--
  (EX (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (Z_non_alias = 1) ” 
  &&  “ (RX = X_non_alias) ” 
  &&  “ (RY = Y_non_alias) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (RY: Z)  (RX: Z)  (ZI: Z) ,
  “ (1 = 1) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (Z_non_alias <> 1) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ (RX = (Zmod (((X_non_alias * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ (RY = (Zmod ((((Y_non_alias * ZI ) * ZI ) * ZI )) (SM2_P_Z))) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_jpoint_to_apoint2_return_wit_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH4 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH5 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH6 : (retval_2 = 1)) (PreH7 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH8 : (Z_non_alias < SM2_P_Z)) (PreH9 : (0 <= Z_non_alias)) (PreH10 : (Y_non_alias < SM2_P_Z)) (PreH11 : (0 <= Y_non_alias)) (PreH12 : (X_non_alias < SM2_P_Z)) (PreH13 : (0 <= X_non_alias)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (Z_non_alias <> 0)) (PreH17 : (retval = 0)) (PreH18 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (Z_non_alias = 1) ” 
  &&  “ (RX = X_non_alias) ” 
  &&  “ (RY = Y_non_alias) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (RY: Z)  (RX: Z)  (ZI: Z) ,
  “ (1 = 1) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (Z_non_alias <> 1) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ (RX = (Zmod (((X_non_alias * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ (RY = (Zmod ((((Y_non_alias * ZI ) * ZI ) * ZI )) (SM2_P_Z))) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition montg_jpoint_to_apoint2_return_wit_3 := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "y") 0 )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (Z_non_alias = 0) ” 
  &&  “ (RX = 0) ” 
  &&  “ (RY = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (r_pre: Z) (Z_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  TT && emp 
|--
  “ (0 < SM2_P_Z) ” 
  &&  “ (0 < SM2_P_Z) ” 
  &&  “ (0 = (mont_p (0))) ” 
  &&  “ (0 = (mont_p (0))) ”
  &&  emp
).

Definition montg_jpoint_to_apoint2_return_wit_3_split_goal_1 := 
forall (r_pre: Z) (Z_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  (0 < SM2_P_Z)
.

Definition montg_jpoint_to_apoint2_return_wit_3_split_goal_2 := 
forall (r_pre: Z) (Z_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  (0 < SM2_P_Z)
.

Definition montg_jpoint_to_apoint2_return_wit_3_split_goal_3 := 
forall (r_pre: Z) (Z_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  (0 = (mont_p (0)))
.

Definition montg_jpoint_to_apoint2_return_wit_3_split_goal_4 := 
forall (r_pre: Z) (Z_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : (retval = 1)) (PreH4 : (Z_non_alias = 0)) (PreH5 : (retval <> 0)) ,
  (0 = (mont_p (0)))
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_2_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_2_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_2_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (Z_non_alias = 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ” 
  &&  “ (retval = 1) ” 
  &&  “ (Z_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (UInt64Array.undef_full (&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_2 := montg_jpoint_to_apoint2_partial_solve_wit_2_pure -> montg_jpoint_to_apoint2_partial_solve_wit_2_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_3_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH2 : (retval = 1)) (PreH3 : (Z_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH2 : (retval = 1)) (PreH3 : (Z_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_3_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH2 : (retval = 1)) (PreH3 : (Z_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_3_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH2 : (retval = 1)) (PreH3 : (Z_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ” 
  &&  “ (retval = 1) ” 
  &&  “ (Z_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (UInt64Array.undef_full (&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") 0 )
  **  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_3 := montg_jpoint_to_apoint2_partial_solve_wit_3_pure -> montg_jpoint_to_apoint2_partial_solve_wit_3_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_4_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Z_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_non_alias))) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (0 <= (mont_p (Z_non_alias))) ” 
  &&  “ ((mont_p (Z_non_alias)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (mont_p (Z_non_alias))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_4_pure_split_goal_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Z_non_alias)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_4_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (Z_non_alias < SM2_P_Z)) (PreH2 : (0 <= Z_non_alias)) (PreH3 : (Y_non_alias < SM2_P_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (Z_non_alias <> 0)) (PreH8 : (retval = 0)) (PreH9 : (Z_non_alias <> 0)) (PreH10 : (retval = 0)) ,
  (store_jpoint_fields a_pre (mont_p (X_non_alias)) (mont_p (Y_non_alias)) (mont_p (Z_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Z_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Z_non_alias))) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_4 := montg_jpoint_to_apoint2_partial_solve_wit_4_pure -> montg_jpoint_to_apoint2_partial_solve_wit_4_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_5_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (X_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_non_alias))) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x")) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ” 
  &&  “ (0 <= (mont_p (X_non_alias))) ” 
  &&  “ ((mont_p (X_non_alias)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (mont_p (X_non_alias))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_5_pure_split_goal_4 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (X_non_alias)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_5_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 1)) (PreH3 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (X_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (X_non_alias))) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_non_alias)) = MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (UInt64Array.undef_full (&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_5 := montg_jpoint_to_apoint2_partial_solve_wit_5_pure -> montg_jpoint_to_apoint2_partial_solve_wit_5_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_6_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Y_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_non_alias))) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "y")) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ” 
  &&  “ (0 <= (mont_p (Y_non_alias))) ” 
  &&  “ ((mont_p (Y_non_alias)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((a_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (mont_p (Y_non_alias))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_6_pure_split_goal_4 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Y_non_alias)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_6_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x"))) (PreH3 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH4 : (retval_2 = 1)) (PreH5 : ((mont_p (Z_non_alias)) = MONTG_ONE_Z)) (PreH6 : (Z_non_alias < SM2_P_Z)) (PreH7 : (0 <= Z_non_alias)) (PreH8 : (Y_non_alias < SM2_P_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (Z_non_alias <> 0)) (PreH15 : (retval = 0)) (PreH16 : (retval_2 <> 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((mont_p (Y_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (Y_non_alias))) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "y")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ ((&((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) = &((r_pre)  # "AFPoint" ->ₛ "x")) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ ((mont_p (Z_non_alias)) = MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (UInt64Array.undef_full (&((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_6 := montg_jpoint_to_apoint2_partial_solve_wit_6_pure -> montg_jpoint_to_apoint2_partial_solve_wit_6_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_7_pure := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= Z_non_alias) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_7_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "T" ) ) )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= Z_non_alias) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UndefStructPredu32 ( &( "Zinv" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_7 := montg_jpoint_to_apoint2_partial_solve_wit_7_pure -> montg_jpoint_to_apoint2_partial_solve_wit_7_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_8_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Z_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_8_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_8_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_8_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (retval_2 = 0)) (PreH3 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH4 : (Z_non_alias < SM2_P_Z)) (PreH5 : (0 <= Z_non_alias)) (PreH6 : (Y_non_alias < SM2_P_Z)) (PreH7 : (0 <= Y_non_alias)) (PreH8 : (X_non_alias < SM2_P_Z)) (PreH9 : (0 <= X_non_alias)) (PreH10 : (Z_non_alias <> 0)) (PreH11 : (retval = 0)) (PreH12 : (Z_non_alias <> 0)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UInt64Array.undef_full &(( &( "Zinv" ) )->ₛ "v") 4 )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Z_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (UInt64Array.undef_full (&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_8 := montg_jpoint_to_apoint2_partial_solve_wit_8_pure -> montg_jpoint_to_apoint2_partial_solve_wit_8_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_9_pure := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_9_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UndefStructPredu32 ( &( "Zisqr" ) ) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (UInt64Array.undef_full &(( &( "Zisqr" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_9 := montg_jpoint_to_apoint2_partial_solve_wit_9_pure -> montg_jpoint_to_apoint2_partial_solve_wit_9_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_10_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_10_pure_split_goal_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_10_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((ZI * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p ((ZI * ZI ))) = (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z))))) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_10 := montg_jpoint_to_apoint2_partial_solve_wit_10_pure -> montg_jpoint_to_apoint2_partial_solve_wit_10_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_11_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_11_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_11_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_11_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) Z_non_alias )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((ZI * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((ZI * ZI )) (SM2_P_Z))) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (UInt64Array.undef_full &(( &( "T" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_11 := montg_jpoint_to_apoint2_partial_solve_wit_11_pure -> montg_jpoint_to_apoint2_partial_solve_wit_11_aux.

Definition montg_jpoint_to_apoint2_partial_solve_wit_12_pure := 
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) (mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Y_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) = (mont_p ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))))) ”
) \/
(
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) (mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) = (mont_p ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))))) ” 
  &&  “ (0 <= (Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
).

Definition montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_1 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) (mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) = (mont_p ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_2 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) (mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= (Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_12_pure_split_goal_3 := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) (mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "ry" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "y"))
  **  ((( &( "rx" ) )) # Ptr  |-> &((r_pre)  # "AFPoint" ->ₛ "x"))
  **  ((( &( "az" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "z"))
  **  ((( &( "ay" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "y"))
  **  ((( &( "ax" ) )) # Ptr  |-> &((a_pre)  # "JPoint" ->ₛ "x"))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ”
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_12_aux := 
forall (r_pre: Z) (a_pre: Z) (Z_non_alias: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (ZI: Z) (PreH1 : ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) ))) (PreH2 : ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) ))) (PreH3 : (0 <= ZI)) (PreH4 : (ZI < SM2_P_Z)) (PreH5 : ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1)) (PreH6 : ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z"))) (PreH7 : (retval_2 = 0)) (PreH8 : ((mont_p (Z_non_alias)) <> MONTG_ONE_Z)) (PreH9 : (Z_non_alias < SM2_P_Z)) (PreH10 : (0 <= Z_non_alias)) (PreH11 : (Y_non_alias < SM2_P_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (Z_non_alias <> 0)) (PreH16 : (retval = 0)) (PreH17 : (Z_non_alias <> 0)) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp ( &( "T" ) ) (mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
|--
  “ (0 <= Y_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ ((mont_p (((Zmod ((ZI * ZI )) (SM2_P_Z)) * ZI ))) = (mont_p ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z))))) ” 
  &&  “ ((&(( &( "T" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "T" ) )) ” 
  &&  “ ((&(( &( "Zinv" ) )->ₛ "v") + (0 * sizeof(UINT64))) = ( &( "Zinv" ) )) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ ((&((a_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) = &((a_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ((mont_p (Z_non_alias)) <> MONTG_ONE_Z) ” 
  &&  “ (Z_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Z_non_alias) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "JPoint" ->ₛ "y") (mont_p (Y_non_alias)) )
  **  (store_fp ( &( "T" ) ) (mont_p ((Zmod (((ZI * ZI ) * ZI )) (SM2_P_Z)))) )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "Zisqr" ) ) (mont_p ((Zmod ((ZI * ZI )) (SM2_P_Z)))) )
  **  (store_fp ( &( "Zinv" ) ) (mont_p (ZI)) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "x") (mont_p (X_non_alias)) )
  **  (store_fp &((r_pre)  # "AFPoint" ->ₛ "x") (mont_p ((X_non_alias * (Zmod ((ZI * ZI )) (SM2_P_Z)) ))) )
  **  (store_fp &((a_pre)  # "JPoint" ->ₛ "z") (mont_p (Z_non_alias)) )
  **  (store_montg_one )
  **  (store_bn_zero )
.

Definition montg_jpoint_to_apoint2_partial_solve_wit_12 := montg_jpoint_to_apoint2_partial_solve_wit_12_pure -> montg_jpoint_to_apoint2_partial_solve_wit_12_aux.

Definition montg_jpoint_to_apoint2_derive_point_non_alias_by_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_point_non_alias: ec_point) ,
  (store_mont_jpoint a_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) (Z_non_alias: Z) ,
  ((store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  **
  (((EX RY RX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (Z_non_alias = 0) ” 
  &&  “ (RX = 0) ” 
  &&  “ (RY = 0) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX RY RX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (Z_non_alias = 1) ” 
  &&  “ (RX = X_non_alias) ” 
  &&  “ (RY = Y_non_alias) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX RY RX ZI retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (Z_non_alias <> 0) ” 
  &&  “ (Z_non_alias <> 1) ” 
  &&  “ (0 <= ZI) ” 
  &&  “ (ZI < SM2_P_Z) ” 
  &&  “ ((Zmod ((Z_non_alias * ZI )) (SM2_P_Z)) = 1) ” 
  &&  “ (RX = (Zmod (((X_non_alias * ZI ) * ZI )) (SM2_P_Z))) ” 
  &&  “ (RY = (Zmod ((((Y_non_alias * ZI ) * ZI ) * ZI )) (SM2_P_Z))) ”
  &&  (store_mont_jpoint_coords a_pre X_non_alias Y_non_alias Z_non_alias )
  **  (store_mont_afpoint_coords r_pre RX RY )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )))
  -*
  (EX retval,
  “ (retval = 1) ”
  &&  (store_mont_jpoint a_pre P_point_non_alias )
  **  (store_mont_afpoint r_pre P_point_non_alias )
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

Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_1 : montg_jpoint_to_apoint2_safety_wit_1.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_2 : montg_jpoint_to_apoint2_safety_wit_2.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_3 : montg_jpoint_to_apoint2_safety_wit_3.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_4 : montg_jpoint_to_apoint2_safety_wit_4.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_5 : montg_jpoint_to_apoint2_safety_wit_5.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_6 : montg_jpoint_to_apoint2_safety_wit_6.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_7 : montg_jpoint_to_apoint2_safety_wit_7.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_8 : montg_jpoint_to_apoint2_safety_wit_8.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_9 : montg_jpoint_to_apoint2_safety_wit_9.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_10 : montg_jpoint_to_apoint2_safety_wit_10.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_11 : montg_jpoint_to_apoint2_safety_wit_11.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_12 : montg_jpoint_to_apoint2_safety_wit_12.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_13 : montg_jpoint_to_apoint2_safety_wit_13.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_14 : montg_jpoint_to_apoint2_safety_wit_14.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_15 : montg_jpoint_to_apoint2_safety_wit_15.
Axiom proof_of_montg_jpoint_to_apoint2_safety_wit_16 : montg_jpoint_to_apoint2_safety_wit_16.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_1_1 : montg_jpoint_to_apoint2_entail_wit_1_1.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_1_2 : montg_jpoint_to_apoint2_entail_wit_1_2.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_2_1 : montg_jpoint_to_apoint2_entail_wit_2_1.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_2_2 : montg_jpoint_to_apoint2_entail_wit_2_2.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_3 : montg_jpoint_to_apoint2_entail_wit_3.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_4 : montg_jpoint_to_apoint2_entail_wit_4.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_5_1 : montg_jpoint_to_apoint2_entail_wit_5_1.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_5_2 : montg_jpoint_to_apoint2_entail_wit_5_2.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_6_1 : montg_jpoint_to_apoint2_entail_wit_6_1.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_6_2 : montg_jpoint_to_apoint2_entail_wit_6_2.
Axiom proof_of_montg_jpoint_to_apoint2_entail_wit_7 : montg_jpoint_to_apoint2_entail_wit_7.
Axiom proof_of_montg_jpoint_to_apoint2_return_wit_1 : montg_jpoint_to_apoint2_return_wit_1.
Axiom proof_of_montg_jpoint_to_apoint2_return_wit_2 : montg_jpoint_to_apoint2_return_wit_2.
Axiom proof_of_montg_jpoint_to_apoint2_return_wit_3 : montg_jpoint_to_apoint2_return_wit_3.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_1 : montg_jpoint_to_apoint2_partial_solve_wit_1.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_2_pure : montg_jpoint_to_apoint2_partial_solve_wit_2_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_2 : montg_jpoint_to_apoint2_partial_solve_wit_2.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_3_pure : montg_jpoint_to_apoint2_partial_solve_wit_3_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_3 : montg_jpoint_to_apoint2_partial_solve_wit_3.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_4_pure : montg_jpoint_to_apoint2_partial_solve_wit_4_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_4 : montg_jpoint_to_apoint2_partial_solve_wit_4.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5_pure : montg_jpoint_to_apoint2_partial_solve_wit_5_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_5 : montg_jpoint_to_apoint2_partial_solve_wit_5.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6_pure : montg_jpoint_to_apoint2_partial_solve_wit_6_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_6 : montg_jpoint_to_apoint2_partial_solve_wit_6.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_7_pure : montg_jpoint_to_apoint2_partial_solve_wit_7_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_7 : montg_jpoint_to_apoint2_partial_solve_wit_7.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_8_pure : montg_jpoint_to_apoint2_partial_solve_wit_8_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_8 : montg_jpoint_to_apoint2_partial_solve_wit_8.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_9_pure : montg_jpoint_to_apoint2_partial_solve_wit_9_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_9 : montg_jpoint_to_apoint2_partial_solve_wit_9.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_10_pure : montg_jpoint_to_apoint2_partial_solve_wit_10_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_10 : montg_jpoint_to_apoint2_partial_solve_wit_10.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_11_pure : montg_jpoint_to_apoint2_partial_solve_wit_11_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_11 : montg_jpoint_to_apoint2_partial_solve_wit_11.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_12_pure : montg_jpoint_to_apoint2_partial_solve_wit_12_pure.
Axiom proof_of_montg_jpoint_to_apoint2_partial_solve_wit_12 : montg_jpoint_to_apoint2_partial_solve_wit_12.
Axiom proof_of_montg_jpoint_to_apoint2_derive_point_non_alias_by_non_alias : montg_jpoint_to_apoint2_derive_point_non_alias_by_non_alias.

End VC_Correct.
