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
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import u32_alias_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_montg_helper_views_strategy_proof.

(*----- Function montg_apoint_to_jpoint2 -----*)

Definition montg_apoint_to_jpoint2_safety_wit_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  ((( &( "ax" ) )) # Ptr  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  ((( &( "ay" ) )) # Ptr  |->_)
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_3 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  ((( &( "az" ) )) # Ptr  |->_)
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_4 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  ((( &( "rx" ) )) # Ptr  |->_)
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_5 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  ((( &( "ry" ) )) # Ptr  |->_)
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_6 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  ((( &( "rz" ) )) # Ptr  |->_)
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_7 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (AX_non_alias = 0)) (PreH3 : (AY_non_alias = 0)) (PreH4 : (retval = 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_apoint_to_jpoint2_safety_wit_8 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (AX_non_alias <> 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_apoint_to_jpoint2_safety_wit_9 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (AY_non_alias <> 0)) (PreH3 : (retval <> 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ False ”
.

Definition montg_apoint_to_jpoint2_safety_wit_10 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (AX_non_alias = 0)) (PreH3 : (AY_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint_coords r_pre 1 1 0 )
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_11 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AX_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_apoint_to_jpoint2_safety_wit_12 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AY_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition montg_apoint_to_jpoint2_entail_wit_1_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (AX_non_alias <> 0)) (PreH3 : (retval = 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (“ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_1_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (AY_non_alias <> 0)) (PreH3 : (retval_2 = 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (“ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_1_3 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_3: Z) (PreH1 : (retval_3 = 1)) (PreH2 : (AX_non_alias = 0)) (PreH3 : (AY_non_alias = 0)) (PreH4 : (retval_3 = 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_2_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (AX_non_alias <> 0)) (PreH3 : (retval_2 <> 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (AX_non_alias = 0) ” 
  &&  “ (AY_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_entail_wit_2_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (AY_non_alias <> 0)) (PreH3 : (retval_2 <> 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  EX (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (AX_non_alias = 0) ” 
  &&  “ (AY_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_entail_wit_2_3 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (AX_non_alias = 0)) (PreH3 : (AY_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (retval = 1) ” 
  &&  “ (AX_non_alias = 0) ” 
  &&  “ (AY_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_entail_wit_3_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (AX_non_alias <> 0)) (PreH3 : (retval = 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (“ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint_fields a_pre (mont_p (AX_non_alias)) (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields a_pre (mont_p (AX_non_alias)) (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_3_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (AY_non_alias <> 0)) (PreH3 : (retval_2 = 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint_fields a_pre (mont_p (AX_non_alias)) (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (“ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields a_pre (mont_p (AX_non_alias)) (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_4_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (AY_non_alias < SM2_P_Z)) (PreH2 : (0 <= AY_non_alias)) (PreH3 : (AX_non_alias < SM2_P_Z)) (PreH4 : (0 <= AX_non_alias)) (PreH5 : (retval = 0)) (PreH6 : (AX_non_alias <> 0)) (PreH7 : (retval = 0)) ,
  (store_afpoint_fields a_pre (mont_p (AX_non_alias)) (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (“ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_4_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : (AY_non_alias < SM2_P_Z)) (PreH2 : (0 <= AY_non_alias)) (PreH3 : (AX_non_alias < SM2_P_Z)) (PreH4 : (0 <= AX_non_alias)) (PreH5 : (retval_2 = 0)) (PreH6 : (AY_non_alias <> 0)) (PreH7 : (retval_2 = 0)) ,
  (store_afpoint_fields a_pre (mont_p (AX_non_alias)) (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (“ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_5_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (AY_non_alias < SM2_P_Z)) (PreH2 : (0 <= AY_non_alias)) (PreH3 : (AX_non_alias < SM2_P_Z)) (PreH4 : (0 <= AX_non_alias)) (PreH5 : (retval = 0)) (PreH6 : (AX_non_alias <> 0)) (PreH7 : (retval = 0)) ,
  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (“ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_5_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : (AY_non_alias < SM2_P_Z)) (PreH2 : (0 <= AY_non_alias)) (PreH3 : (AX_non_alias < SM2_P_Z)) (PreH4 : (0 <= AX_non_alias)) (PreH5 : (retval_2 = 0)) (PreH6 : (AY_non_alias <> 0)) (PreH7 : (retval_2 = 0)) ,
  (store_fp &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_fp &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (“ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_6_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AX_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AX_non_alias)) )
  **  (store_u256_limbs (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (“ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_6_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval_2 = 0)) (PreH10 : (AY_non_alias <> 0)) (PreH11 : (retval_2 = 0)) ,
  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AX_non_alias)) )
  **  (store_u256_limbs (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (“ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_7_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AX_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AY_non_alias)) )
  **  (store_u256_limbs (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (“ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (EX (retval_2: Z) ,
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_7_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval_2 = 0)) (PreH10 : (AY_non_alias <> 0)) (PreH11 : (retval_2 = 0)) ,
  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AY_non_alias)) )
  **  (store_u256_limbs (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  (EX (retval: Z) ,
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
  ||
  (“ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_entail_wit_8_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AX_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256_limbs ( &( "MONTG_ONE" ) ) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (retval_2: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
.

Definition montg_apoint_to_jpoint2_entail_wit_8_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval_2 = 0)) (PreH10 : (AY_non_alias <> 0)) (PreH11 : (retval_2 = 0)) ,
  (store_u256_limbs ( &( "MONTG_ONE" ) ) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  (EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (retval: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
  ||
  (EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 ))
.

Definition montg_apoint_to_jpoint2_entail_wit_9_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AX_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256_limbs (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (“ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (EX (retval_2: Z)  (x0_2: Z)  (x1_2: Z)  (x2_2: Z)  (x3_2: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_apoint_to_jpoint2_entail_wit_9_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval_2: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval_2 = 0)) (PreH19 : (AY_non_alias <> 0)) (PreH20 : (retval_2 = 0)) ,
  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256_limbs (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
|--
  (EX (retval: Z)  (x0: Z)  (x1: Z)  (x2: Z)  (x3: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
  ||
  (“ (MONTG_ONE_Z = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  ((( &( "rz" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ry" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "rx" ) )) # Ptr  |-> (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "az" ) )) # Ptr  |-> (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))))
  **  ((( &( "ay" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "ax" ) )) # Ptr  |-> (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre))
.

Definition montg_apoint_to_jpoint2_return_wit_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AX_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
|--
  (EX (RZ: Z)  (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (RX = AX_non_alias) ” 
  &&  “ (RY = AY_non_alias) ” 
  &&  “ (RZ = 1) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one ))
  ||
  (EX (RZ: Z)  (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (RX = AX_non_alias) ” 
  &&  “ (RY = AY_non_alias) ” 
  &&  “ (RZ = 1) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_return_wit_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AY_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "z") MONTG_ONE_Z )
  **  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
|--
  (EX (RZ: Z)  (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (RX = AX_non_alias) ” 
  &&  “ (RY = AY_non_alias) ” 
  &&  “ (RZ = 1) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one ))
  ||
  (EX (RZ: Z)  (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (RX = AX_non_alias) ” 
  &&  “ (RY = AY_non_alias) ” 
  &&  “ (RZ = 1) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one ))
.

Definition montg_apoint_to_jpoint2_return_wit_3 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (AX_non_alias = 0)) (PreH3 : (AY_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_montg_one )
  **  (store_mont_jpoint_coords r_pre 1 1 0 )
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
|--
  EX (RZ: Z)  (RY: Z)  (RX: Z) ,
  “ (1 = 1) ” 
  &&  “ (AX_non_alias = 0) ” 
  &&  “ (AY_non_alias = 0) ” 
  &&  “ (RX = 1) ” 
  &&  “ (RY = 1) ” 
  &&  “ (RZ = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_1 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_2 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (AX_non_alias = 0)) (PreH3 : (AY_non_alias = 0)) (PreH4 : (retval <> 0)) ,
  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ (retval = 1) ” 
  &&  “ (AX_non_alias = 0) ” 
  &&  “ (AY_non_alias = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_montg_one )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_bn_zero )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_3 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AX_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AX_non_alias)) )
  **  (UInt64Array.undef_full (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_4 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AY_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AX_non_alias)) )
  **  (UInt64Array.undef_full (&((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_5 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AX_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AY_non_alias)) )
  **  (UInt64Array.undef_full (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_6 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AY_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((a_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) (mont_p (AY_non_alias)) )
  **  (UInt64Array.undef_full (&((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_7 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AY_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_montg_one )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_8 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (PreH1 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH2 : (0 <= (mont_p (AX_non_alias)))) (PreH3 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH4 : (0 <= (mont_p (AY_non_alias)))) (PreH5 : (AY_non_alias < SM2_P_Z)) (PreH6 : (0 <= AY_non_alias)) (PreH7 : (AX_non_alias < SM2_P_Z)) (PreH8 : (0 <= AX_non_alias)) (PreH9 : (retval = 0)) (PreH10 : (AX_non_alias <> 0)) (PreH11 : (retval = 0)) ,
  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_montg_one )
|--
  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_montg_one )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_9 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AX_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (UInt64Array.undef_full (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
.

Definition montg_apoint_to_jpoint2_partial_solve_wit_10 := 
forall (r_pre: Z) (a_pre: Z) (AY_non_alias: Z) (AX_non_alias: Z) (retval: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : ((mont_p (AX_non_alias)) < SM2_P_Z)) (PreH11 : (0 <= (mont_p (AX_non_alias)))) (PreH12 : ((mont_p (AY_non_alias)) < SM2_P_Z)) (PreH13 : (0 <= (mont_p (AY_non_alias)))) (PreH14 : (AY_non_alias < SM2_P_Z)) (PreH15 : (0 <= AY_non_alias)) (PreH16 : (AX_non_alias < SM2_P_Z)) (PreH17 : (0 <= AX_non_alias)) (PreH18 : (retval = 0)) (PreH19 : (AY_non_alias <> 0)) (PreH20 : (retval = 0)) ,
  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((mont_p (AX_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AX_non_alias))) ” 
  &&  “ ((mont_p (AY_non_alias)) < SM2_P_Z) ” 
  &&  “ (0 <= (mont_p (AY_non_alias))) ” 
  &&  “ (AY_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AY_non_alias) ” 
  &&  “ (AX_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= AX_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64))) MONTG_ONE_Z )
  **  (UInt64Array.undef_full (&((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64))) 4 )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "y") (mont_p (AY_non_alias)) )
  **  (store_u256 &((r_pre)  # "JPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_u256 &((a_pre)  # "AFPoint" ->ₛ "x") (mont_p (AX_non_alias)) )
  **  (store_bn_zero )
.

Definition montg_apoint_to_jpoint2_which_implies_wit_1 := 
(
  (store_montg_one )
|--
  (store_u256_limbs ( &( "MONTG_ONE" ) ) MONTG_ONE_Z )
) \/
(
  (store_montg_one )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (MONTG_ONE_Z = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ”
  &&  (((( &( "MONTG_ONE" ) ) + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((( &( "MONTG_ONE" ) ) + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((( &( "MONTG_ONE" ) ) + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((( &( "MONTG_ONE" ) ) + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition montg_apoint_to_jpoint2_derive_point_non_alias_by_non_alias := 
forall (r_pre: Z) (a_pre: Z) (P_point_non_alias: ec_point) ,
  (store_mont_afpoint a_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
EX (AX_non_alias: Z) (AY_non_alias: Z) ,
  ((store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one ))
  **
  (((EX RZ RY RX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (AX_non_alias = 0) ” 
  &&  “ (AY_non_alias = 0) ” 
  &&  “ (RX = 1) ” 
  &&  “ (RY = 1) ” 
  &&  “ (RZ = 0) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one ))
  ||
  (EX RZ RY RX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (AY_non_alias <> 0) ” 
  &&  “ (RX = AX_non_alias) ” 
  &&  “ (RY = AY_non_alias) ” 
  &&  “ (RZ = 1) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one ))
  ||
  (EX RZ RY RX retval_2,
  “ (retval_2 = 1) ” 
  &&  “ (AX_non_alias <> 0) ” 
  &&  “ (RX = AX_non_alias) ” 
  &&  “ (RY = AY_non_alias) ” 
  &&  “ (RZ = 1) ”
  &&  (store_mont_afpoint_coords a_pre AX_non_alias AY_non_alias )
  **  (store_mont_jpoint_coords r_pre RX RY RZ )
  **  (store_bn_zero )
  **  (store_montg_one )))
  -*
  (EX retval,
  “ (retval = 1) ”
  &&  (store_mont_afpoint a_pre P_point_non_alias )
  **  (store_mont_jpoint r_pre P_point_non_alias )
  **  (store_bn_zero )
  **  (store_montg_one )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include u32_alias_Strategy_Correct.
Include ecc_montg_helper_views_Strategy_Correct.

Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_1 : montg_apoint_to_jpoint2_safety_wit_1.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_2 : montg_apoint_to_jpoint2_safety_wit_2.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_3 : montg_apoint_to_jpoint2_safety_wit_3.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_4 : montg_apoint_to_jpoint2_safety_wit_4.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_5 : montg_apoint_to_jpoint2_safety_wit_5.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_6 : montg_apoint_to_jpoint2_safety_wit_6.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_7 : montg_apoint_to_jpoint2_safety_wit_7.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_8 : montg_apoint_to_jpoint2_safety_wit_8.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_9 : montg_apoint_to_jpoint2_safety_wit_9.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_10 : montg_apoint_to_jpoint2_safety_wit_10.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_11 : montg_apoint_to_jpoint2_safety_wit_11.
Axiom proof_of_montg_apoint_to_jpoint2_safety_wit_12 : montg_apoint_to_jpoint2_safety_wit_12.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_1_1 : montg_apoint_to_jpoint2_entail_wit_1_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_1_2 : montg_apoint_to_jpoint2_entail_wit_1_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_1_3 : montg_apoint_to_jpoint2_entail_wit_1_3.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_2_1 : montg_apoint_to_jpoint2_entail_wit_2_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_2_2 : montg_apoint_to_jpoint2_entail_wit_2_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_2_3 : montg_apoint_to_jpoint2_entail_wit_2_3.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_3_1 : montg_apoint_to_jpoint2_entail_wit_3_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_3_2 : montg_apoint_to_jpoint2_entail_wit_3_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_4_1 : montg_apoint_to_jpoint2_entail_wit_4_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_4_2 : montg_apoint_to_jpoint2_entail_wit_4_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_5_1 : montg_apoint_to_jpoint2_entail_wit_5_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_5_2 : montg_apoint_to_jpoint2_entail_wit_5_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_6_1 : montg_apoint_to_jpoint2_entail_wit_6_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_6_2 : montg_apoint_to_jpoint2_entail_wit_6_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_7_1 : montg_apoint_to_jpoint2_entail_wit_7_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_7_2 : montg_apoint_to_jpoint2_entail_wit_7_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_8_1 : montg_apoint_to_jpoint2_entail_wit_8_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_8_2 : montg_apoint_to_jpoint2_entail_wit_8_2.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_9_1 : montg_apoint_to_jpoint2_entail_wit_9_1.
Axiom proof_of_montg_apoint_to_jpoint2_entail_wit_9_2 : montg_apoint_to_jpoint2_entail_wit_9_2.
Axiom proof_of_montg_apoint_to_jpoint2_return_wit_1 : montg_apoint_to_jpoint2_return_wit_1.
Axiom proof_of_montg_apoint_to_jpoint2_return_wit_2 : montg_apoint_to_jpoint2_return_wit_2.
Axiom proof_of_montg_apoint_to_jpoint2_return_wit_3 : montg_apoint_to_jpoint2_return_wit_3.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_1 : montg_apoint_to_jpoint2_partial_solve_wit_1.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_2 : montg_apoint_to_jpoint2_partial_solve_wit_2.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_3 : montg_apoint_to_jpoint2_partial_solve_wit_3.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_4 : montg_apoint_to_jpoint2_partial_solve_wit_4.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_5 : montg_apoint_to_jpoint2_partial_solve_wit_5.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_6 : montg_apoint_to_jpoint2_partial_solve_wit_6.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_7 : montg_apoint_to_jpoint2_partial_solve_wit_7.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_8 : montg_apoint_to_jpoint2_partial_solve_wit_8.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_9 : montg_apoint_to_jpoint2_partial_solve_wit_9.
Axiom proof_of_montg_apoint_to_jpoint2_partial_solve_wit_10 : montg_apoint_to_jpoint2_partial_solve_wit_10.
Axiom proof_of_montg_apoint_to_jpoint2_which_implies_wit_1 : montg_apoint_to_jpoint2_which_implies_wit_1.
Axiom proof_of_montg_apoint_to_jpoint2_derive_point_non_alias_by_non_alias : montg_apoint_to_jpoint2_derive_point_non_alias_by_non_alias.

End VC_Correct.
