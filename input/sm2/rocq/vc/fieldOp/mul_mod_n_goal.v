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
      SimpleC.EE.Applications_human.sm2.lib.fieldOp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.

(*----- Function mul_mod_n -----*)

Definition mul_mod_n_safety_wit_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition mul_mod_n_safety_wit_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition mul_mod_n_safety_wit_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (Y_non_alias = 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition mul_mod_n_safety_wit_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (Y_non_alias <> 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ False ”
.

Definition mul_mod_n_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_2 = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_2_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_2 <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (X_non_alias = 1) ”
  &&  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (X_non_alias = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_5_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_N_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_N_Z)) (PreH4 : (0 <= X_non_alias)) (PreH5 : (X_non_alias = 1)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_6_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (Y_non_alias = 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_3 = 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Y_non_alias <> 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_6_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (Y_non_alias <> 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Y_non_alias <> 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_7_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (Y_non_alias = 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (Y_non_alias = 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_7_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (Y_non_alias <> 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_3 <> 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (Y_non_alias = 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_8_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (Y_non_alias = 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 <> 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_9_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (X_non_alias <> 1)) (PreH2 : (Y_non_alias = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_10_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_N_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_N_Z)) (PreH4 : (0 <= X_non_alias)) (PreH5 : (X_non_alias <> 1)) (PreH6 : (Y_non_alias = 1)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_entail_wit_11_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (R: Z) (K: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (Y_non_alias <> 1)) (PreH8 : (Y_non_alias < SM2_N_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 0)) (PreH13 : (X_non_alias <> 1)) (PreH14 : (X_non_alias < SM2_N_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (retval = 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_nh )
|--
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Y_non_alias <> 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn ( &( "SM2_NH" ) ) SM2_NH_Z )
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition mul_mod_n_return_wit_1_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre (Zmod ((X_non_alias * Y_non_alias )) (SM2_N_Z)) )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  TT && emp 
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = X_non_alias) ” 
  &&  “ (0 <= (Zmod ((X_non_alias * 1 )) (SM2_N_Z))) ” 
  &&  “ ((Zmod ((X_non_alias * 1 )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_non_alias * 1 )) (SM2_N_Z))) ”
  &&  emp
).

Definition mul_mod_n_return_wit_1_non_alias_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = X_non_alias)
.

Definition mul_mod_n_return_wit_1_non_alias_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  (0 <= (Zmod ((X_non_alias * 1 )) (SM2_N_Z)))
.

Definition mul_mod_n_return_wit_1_non_alias_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  ((Zmod ((X_non_alias * 1 )) (SM2_N_Z)) < SM2_N_Z)
.

Definition mul_mod_n_return_wit_1_non_alias_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((X_non_alias * 1 )) (SM2_N_Z)))
.

Definition mul_mod_n_return_wit_2_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))) )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre (Zmod ((X_non_alias * Y_non_alias )) (SM2_N_Z)) )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  TT && emp 
|--
  “ ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = Y_non_alias) ” 
  &&  “ (0 <= (Zmod ((1 * Y_non_alias )) (SM2_N_Z))) ” 
  &&  “ ((Zmod ((1 * Y_non_alias )) (SM2_N_Z)) < SM2_N_Z) ” 
  &&  “ ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = (Zmod ((1 * Y_non_alias )) (SM2_N_Z))) ”
  &&  emp
).

Definition mul_mod_n_return_wit_2_non_alias_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = Y_non_alias)
.

Definition mul_mod_n_return_wit_2_non_alias_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  (0 <= (Zmod ((1 * Y_non_alias )) (SM2_N_Z)))
.

Definition mul_mod_n_return_wit_2_non_alias_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  ((Zmod ((1 * Y_non_alias )) (SM2_N_Z)) < SM2_N_Z)
.

Definition mul_mod_n_return_wit_2_non_alias_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  ((u64_list_value ((cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))))) = (Zmod ((1 * Y_non_alias )) (SM2_N_Z)))
.

Definition mul_mod_n_return_wit_3_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (R: Z) (K: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((R * SM2_NH_Z ) + (K_2 * SM2_N_Z ) ))) (PreH4 : (result_pre = result_pre)) (PreH5 : (0 <= R)) (PreH6 : (R < SM2_N_Z)) (PreH7 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (Y_non_alias <> 1)) (PreH12 : (Y_non_alias < SM2_N_Z)) (PreH13 : (0 <= Y_non_alias)) (PreH14 : (0 <= retval)) (PreH15 : (retval <= 1)) (PreH16 : (retval = 0)) (PreH17 : (X_non_alias <> 1)) (PreH18 : (X_non_alias < SM2_N_Z)) (PreH19 : (0 <= X_non_alias)) (PreH20 : (retval = 0)) (PreH21 : (retval_2 = 0)) ,
  (store_fn result_pre R_2 )
  **  (store_fn ( &( "SM2_NH" ) ) SM2_NH_Z )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
|--
  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre (Zmod ((X_non_alias * Y_non_alias )) (SM2_N_Z)) )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (R: Z) (K: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((R * SM2_NH_Z ) + (K_2 * SM2_N_Z ) ))) (PreH4 : (0 <= R)) (PreH5 : (R < SM2_N_Z)) (PreH6 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (Y_non_alias <> 1)) (PreH11 : (Y_non_alias < SM2_N_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (X_non_alias <> 1)) (PreH17 : (X_non_alias < SM2_N_Z)) (PreH18 : (0 <= X_non_alias)) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  TT && emp 
|--
  “ (R_2 = (Zmod ((X_non_alias * Y_non_alias )) (SM2_N_Z))) ”
  &&  emp
).

Definition mul_mod_n_return_wit_3_non_alias_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (R: Z) (K: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((R * SM2_NH_Z ) + (K_2 * SM2_N_Z ) ))) (PreH4 : (0 <= R)) (PreH5 : (R < SM2_N_Z)) (PreH6 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH7 : (0 <= retval_2)) (PreH8 : (retval_2 <= 1)) (PreH9 : (retval_2 = 0)) (PreH10 : (Y_non_alias <> 1)) (PreH11 : (Y_non_alias < SM2_N_Z)) (PreH12 : (0 <= Y_non_alias)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (X_non_alias <> 1)) (PreH17 : (X_non_alias < SM2_N_Z)) (PreH18 : (0 <= X_non_alias)) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (R_2 = (Zmod ((X_non_alias * Y_non_alias )) (SM2_N_Z)))
.

Definition mul_mod_n_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) ,
  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_partial_solve_wit_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((y_pre)  # "u32" ->ₛ "v") 4 (cons (x0_2) ((cons (x1_2) ((cons (x2_2) ((cons (x3_2) ((@nil Z))))))))) )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_partial_solve_wit_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (x0_2: Z) (x1_2: Z) (x2_2: Z) (x3_2: Z) (PreH1 : (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)))) (PreH2 : (x3_2 < U64_MOD)) (PreH3 : (0 <= x3_2)) (PreH4 : (x2_2 < U64_MOD)) (PreH5 : (0 <= x2_2)) (PreH6 : (x1_2 < U64_MOD)) (PreH7 : (0 <= x1_2)) (PreH8 : (x0_2 < U64_MOD)) (PreH9 : (0 <= x0_2)) (PreH10 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH11 : (x3 < U64_MOD)) (PreH12 : (0 <= x3)) (PreH13 : (x2 < U64_MOD)) (PreH14 : (0 <= x2)) (PreH15 : (x1 < U64_MOD)) (PreH16 : (0 <= x1)) (PreH17 : (x0 < U64_MOD)) (PreH18 : (0 <= x0)) (PreH19 : (Y_non_alias < SM2_N_Z)) (PreH20 : (0 <= Y_non_alias)) (PreH21 : (X_non_alias < SM2_N_Z)) (PreH22 : (0 <= X_non_alias)) (PreH23 : (X_non_alias <> 1)) (PreH24 : (Y_non_alias = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (Y_non_alias = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition mul_mod_n_partial_solve_wit_5_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (Y_non_alias <> 1)) (PreH5 : (Y_non_alias < SM2_N_Z)) (PreH6 : (0 <= Y_non_alias)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (X_non_alias <> 1)) (PreH11 : (X_non_alias < SM2_N_Z)) (PreH12 : (0 <= X_non_alias)) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_nh )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Y_non_alias <> 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_sm2_nh )
.

Definition mul_mod_n_partial_solve_wit_6_non_alias_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (R: Z) (K: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (Y_non_alias <> 1)) (PreH8 : (Y_non_alias < SM2_N_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 0)) (PreH13 : (X_non_alias <> 1)) (PreH14 : (X_non_alias < SM2_N_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (retval = 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "SM2_NH" ) ) SM2_NH_Z )
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (result_pre = result_pre) ”
.

Definition mul_mod_n_partial_solve_wit_6_non_alias_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (retval: Z) (retval_2: Z) (R: Z) (K: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (Y_non_alias <> 1)) (PreH8 : (Y_non_alias < SM2_N_Z)) (PreH9 : (0 <= Y_non_alias)) (PreH10 : (0 <= retval)) (PreH11 : (retval <= 1)) (PreH12 : (retval = 0)) (PreH13 : (X_non_alias <> 1)) (PreH14 : (X_non_alias < SM2_N_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (retval = 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fn ( &( "SM2_NH" ) ) SM2_NH_Z )
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (result_pre = result_pre) ” 
  &&  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) )) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Y_non_alias <> 1) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fn result_pre R )
  **  (store_fn ( &( "SM2_NH" ) ) SM2_NH_Z )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
.

Definition mul_mod_n_partial_solve_wit_6_non_alias := mul_mod_n_partial_solve_wit_6_non_alias_pure -> mul_mod_n_partial_solve_wit_6_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_mul_mod_n_safety_wit_1_non_alias : mul_mod_n_safety_wit_1_non_alias.
Axiom proof_of_mul_mod_n_safety_wit_2_non_alias : mul_mod_n_safety_wit_2_non_alias.
Axiom proof_of_mul_mod_n_safety_wit_3_non_alias : mul_mod_n_safety_wit_3_non_alias.
Axiom proof_of_mul_mod_n_safety_wit_4_non_alias : mul_mod_n_safety_wit_4_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_1_1_non_alias : mul_mod_n_entail_wit_1_1_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_1_2_non_alias : mul_mod_n_entail_wit_1_2_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_2_1_non_alias : mul_mod_n_entail_wit_2_1_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_2_2_non_alias : mul_mod_n_entail_wit_2_2_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_3_non_alias : mul_mod_n_entail_wit_3_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_4_non_alias : mul_mod_n_entail_wit_4_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_5_non_alias : mul_mod_n_entail_wit_5_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_6_1_non_alias : mul_mod_n_entail_wit_6_1_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_6_2_non_alias : mul_mod_n_entail_wit_6_2_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_7_1_non_alias : mul_mod_n_entail_wit_7_1_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_7_2_non_alias : mul_mod_n_entail_wit_7_2_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_8_non_alias : mul_mod_n_entail_wit_8_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_9_non_alias : mul_mod_n_entail_wit_9_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_10_non_alias : mul_mod_n_entail_wit_10_non_alias.
Axiom proof_of_mul_mod_n_entail_wit_11_non_alias : mul_mod_n_entail_wit_11_non_alias.
Axiom proof_of_mul_mod_n_return_wit_1_non_alias : mul_mod_n_return_wit_1_non_alias.
Axiom proof_of_mul_mod_n_return_wit_2_non_alias : mul_mod_n_return_wit_2_non_alias.
Axiom proof_of_mul_mod_n_return_wit_3_non_alias : mul_mod_n_return_wit_3_non_alias.
Axiom proof_of_mul_mod_n_partial_solve_wit_1_non_alias : mul_mod_n_partial_solve_wit_1_non_alias.
Axiom proof_of_mul_mod_n_partial_solve_wit_2_non_alias : mul_mod_n_partial_solve_wit_2_non_alias.
Axiom proof_of_mul_mod_n_partial_solve_wit_3_non_alias : mul_mod_n_partial_solve_wit_3_non_alias.
Axiom proof_of_mul_mod_n_partial_solve_wit_4_non_alias : mul_mod_n_partial_solve_wit_4_non_alias.
Axiom proof_of_mul_mod_n_partial_solve_wit_5_non_alias : mul_mod_n_partial_solve_wit_5_non_alias.
Axiom proof_of_mul_mod_n_partial_solve_wit_6_non_alias_pure : mul_mod_n_partial_solve_wit_6_non_alias_pure.
Axiom proof_of_mul_mod_n_partial_solve_wit_6_non_alias : mul_mod_n_partial_solve_wit_6_non_alias.

End VC_Correct.
