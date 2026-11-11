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
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basicop_facts_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import basicop_facts_strategy_proof.

(*----- Function sm2n_mong_mul -----*)

Definition sm2n_mong_mul_safety_wit_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_N_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_N_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_N_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_N_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_3_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_N_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_N_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_4_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (Y_r_eq_x < SM2_N_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (X_r_eq_x < SM2_N_Z)) (PreH4 : (0 <= X_r_eq_x)) (PreH5 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_5_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (Y_r_eq_x < SM2_N_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (X_r_eq_x < SM2_N_Z)) (PreH4 : (0 <= X_r_eq_x)) (PreH5 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_6_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (Y_r_eq_x < SM2_N_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (X_r_eq_x < SM2_N_Z)) (PreH4 : (0 <= X_r_eq_x)) (PreH5 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_7_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH2 : (0 <= (X_non_alias * Y_non_alias ))) (PreH3 : ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH4 : (0 <= (Y_non_alias * X_non_alias ))) (PreH5 : (0 <= (X_non_alias * Y_non_alias ))) (PreH6 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH7 : (Y_non_alias < SM2_N_Z)) (PreH8 : (0 <= Y_non_alias)) (PreH9 : (X_non_alias < SM2_N_Z)) (PreH10 : (0 <= X_non_alias)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_safety_wit_8_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH2 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH3 : ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH4 : (0 <= (Y_r_eq_x * X_r_eq_x ))) (PreH5 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH6 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH7 : (Y_r_eq_x < SM2_N_Z)) (PreH8 : (0 <= Y_r_eq_x)) (PreH9 : (X_r_eq_x < SM2_N_Z)) (PreH10 : (0 <= X_r_eq_x)) (PreH11 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2n_mong_mul_entail_wit_1_1_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (result_pre = x_pre)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn x_pre X_r_eq_x )
  **  (store_fn y_pre Y_r_eq_x )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition sm2n_mong_mul_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition sm2n_mong_mul_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (0 <= (X_non_alias * Y_non_alias ))) (PreH2 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH3 : (Y_non_alias < SM2_N_Z)) (PreH4 : (0 <= Y_non_alias)) (PreH5 : (X_non_alias < SM2_N_Z)) (PreH6 : (0 <= X_non_alias)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_non_alias * X_non_alias )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_r_eq_x * X_r_eq_x )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition sm2n_mong_mul_entail_wit_2_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH2 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH3 : (Y_r_eq_x < SM2_N_Z)) (PreH4 : (0 <= Y_r_eq_x)) (PreH5 : (X_r_eq_x < SM2_N_Z)) (PreH6 : (0 <= X_r_eq_x)) (PreH7 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  (“ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_non_alias * X_non_alias )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
  ||
  (“ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_r_eq_x * X_r_eq_x )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n ))
.

Definition sm2n_mong_mul_entail_wit_3_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (K: Z) (R: Z) (PreH1 : (0 <= R)) (PreH2 : (R < SM2_N_Z)) (PreH3 : ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) ))) (PreH4 : ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH5 : (0 <= (X_non_alias * Y_non_alias ))) (PreH6 : ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH7 : (0 <= (Y_non_alias * X_non_alias ))) (PreH8 : (0 <= (X_non_alias * Y_non_alias ))) (PreH9 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH10 : (Y_non_alias < SM2_N_Z)) (PreH11 : (0 <= Y_non_alias)) (PreH12 : (X_non_alias < SM2_N_Z)) (PreH13 : (0 <= X_non_alias)) ,
  (UInt64Array.full_shape (( &( "interim" ) ) + (0 * sizeof(UINT64))) 9 )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_non_alias * X_non_alias )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (K_2: Z)  (R_2: Z) ,
  “ (0 <= R_2) ” 
  &&  “ (R_2 < SM2_N_Z) ” 
  &&  “ ((R_2 * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K_2 * SM2_N_Z ) )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_r_eq_x * X_r_eq_x )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fn result_pre R_2 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sm2n_mong_mul_entail_wit_3_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K_2 * SM2_N_Z ) ))) (PreH4 : ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH5 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH6 : ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH7 : (0 <= (Y_r_eq_x * X_r_eq_x ))) (PreH8 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH9 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH10 : (Y_r_eq_x < SM2_N_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (X_r_eq_x < SM2_N_Z)) (PreH13 : (0 <= X_r_eq_x)) (PreH14 : (result_pre = x_pre)) ,
  (UInt64Array.full_shape (( &( "interim" ) ) + (0 * sizeof(UINT64))) 9 )
  **  (store_fn result_pre R_2 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (K: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_non_alias * X_non_alias )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (0 <= R_2) ” 
  &&  “ (R_2 < SM2_N_Z) ” 
  &&  “ ((R_2 * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K_2 * SM2_N_Z ) )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_r_eq_x * X_r_eq_x )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fn result_pre R_2 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sm2n_mong_mul_return_wit_1_non_alias := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K_2 * SM2_N_Z ) ))) (PreH4 : ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH5 : (0 <= (X_non_alias * Y_non_alias ))) (PreH6 : ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH7 : (0 <= (Y_non_alias * X_non_alias ))) (PreH8 : (0 <= (X_non_alias * Y_non_alias ))) (PreH9 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH10 : (Y_non_alias < SM2_N_Z)) (PreH11 : (0 <= Y_non_alias)) (PreH12 : (X_non_alias < SM2_N_Z)) (PreH13 : (0 <= X_non_alias)) ,
  (store_fn result_pre R_2 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
|--
  EX (K: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ ((R * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) )) ”
  &&  (store_fn x_pre X_non_alias )
  **  (store_fn y_pre Y_non_alias )
  **  (store_fn result_pre R )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K_2 * SM2_N_Z ) ))) (PreH4 : ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH5 : (0 <= (X_non_alias * Y_non_alias ))) (PreH6 : ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH7 : (0 <= (Y_non_alias * X_non_alias ))) (PreH8 : (0 <= (X_non_alias * Y_non_alias ))) (PreH9 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH10 : (Y_non_alias < SM2_N_Z)) (PreH11 : (0 <= Y_non_alias)) (PreH12 : (X_non_alias < SM2_N_Z)) (PreH13 : (0 <= X_non_alias)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
|--
  EX (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (K: Z) ,
  “ (Y_non_alias = (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (0 <= R_2) ” 
  &&  “ (R_2 < SM2_N_Z) ” 
  &&  “ ((R_2 * U256_MOD ) = ((X_non_alias * Y_non_alias ) + (K * SM2_N_Z ) )) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition sm2n_mong_mul_return_wit_2_r_eq_x := 
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K_2 * SM2_N_Z ) ))) (PreH4 : ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH5 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH6 : ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH7 : (0 <= (Y_r_eq_x * X_r_eq_x ))) (PreH8 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH9 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH10 : (Y_r_eq_x < SM2_N_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (X_r_eq_x < SM2_N_Z)) (PreH13 : (0 <= X_r_eq_x)) (PreH14 : (result_pre = x_pre)) ,
  (store_fn result_pre R_2 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
|--
  EX (K: Z)  (R: Z) ,
  “ (0 <= R) ” 
  &&  “ (R < SM2_N_Z) ” 
  &&  “ ((R * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K * SM2_N_Z ) )) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_fn result_pre R )
  **  (store_fn y_pre Y_r_eq_x )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
) \/
(
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (K_2: Z) (R_2: Z) (PreH1 : (0 <= R_2)) (PreH2 : (R_2 < SM2_N_Z)) (PreH3 : ((R_2 * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K_2 * SM2_N_Z ) ))) (PreH4 : ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH5 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH6 : ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH7 : (0 <= (Y_r_eq_x * X_r_eq_x ))) (PreH8 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH9 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH10 : (Y_r_eq_x < SM2_N_Z)) (PreH11 : (0 <= Y_r_eq_x)) (PreH12 : (X_r_eq_x < SM2_N_Z)) (PreH13 : (0 <= X_r_eq_x)) (PreH14 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (K: Z) ,
  “ (Y_r_eq_x = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (0 <= R_2) ” 
  &&  “ (R_2 < SM2_N_Z) ” 
  &&  “ ((R_2 * U256_MOD ) = ((X_r_eq_x * Y_r_eq_x ) + (K * SM2_N_Z ) )) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (((&((y_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition sm2n_mong_mul_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias < SM2_N_Z)) (PreH2 : (0 <= Y_non_alias)) (PreH3 : (X_non_alias < SM2_N_Z)) (PreH4 : (0 <= X_non_alias)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_non_alias )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (UInt64Array.undef_full (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition sm2n_mong_mul_partial_solve_wit_2_r_eq_x := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : (Y_r_eq_x < SM2_N_Z)) (PreH2 : (0 <= Y_r_eq_x)) (PreH3 : (X_r_eq_x < SM2_N_Z)) (PreH4 : (0 <= X_r_eq_x)) (PreH5 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 y_pre Y_r_eq_x )
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (UInt64Array.undef_full (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
.

Definition sm2n_mong_mul_partial_solve_wit_3_non_alias_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH2 : (0 <= (X_non_alias * Y_non_alias ))) (PreH3 : ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH4 : (0 <= (Y_non_alias * X_non_alias ))) (PreH5 : (0 <= (X_non_alias * Y_non_alias ))) (PreH6 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH7 : (Y_non_alias < SM2_N_Z)) (PreH8 : (0 <= Y_non_alias)) (PreH9 : (X_non_alias < SM2_N_Z)) (PreH10 : (0 <= X_non_alias)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ”
.

Definition sm2n_mong_mul_partial_solve_wit_3_non_alias_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH2 : (0 <= (X_non_alias * Y_non_alias ))) (PreH3 : ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD ))) (PreH4 : (0 <= (Y_non_alias * X_non_alias ))) (PreH5 : (0 <= (X_non_alias * Y_non_alias ))) (PreH6 : ((X_non_alias * Y_non_alias ) < U512_MOD)) (PreH7 : (Y_non_alias < SM2_N_Z)) (PreH8 : (0 <= Y_non_alias)) (PreH9 : (X_non_alias < SM2_N_Z)) (PreH10 : (0 <= X_non_alias)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((Y_non_alias * X_non_alias ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_non_alias * X_non_alias )) ” 
  &&  “ (0 <= (X_non_alias * Y_non_alias )) ” 
  &&  “ ((X_non_alias * Y_non_alias ) < U512_MOD) ” 
  &&  “ (Y_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ (X_non_alias < SM2_N_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * Y_non_alias ) )
  **  ((((( &( "interim" ) ) + (0 * sizeof(UINT64))) + (8 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_non_alias )
.

Definition sm2n_mong_mul_partial_solve_wit_3_non_alias := sm2n_mong_mul_partial_solve_wit_3_non_alias_pure -> sm2n_mong_mul_partial_solve_wit_3_non_alias_aux.

Definition sm2n_mong_mul_partial_solve_wit_4_r_eq_x_pure := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH2 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH3 : ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH4 : (0 <= (Y_r_eq_x * X_r_eq_x ))) (PreH5 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH6 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH7 : (Y_r_eq_x < SM2_N_Z)) (PreH8 : (0 <= Y_r_eq_x)) (PreH9 : (X_r_eq_x < SM2_N_Z)) (PreH10 : (0 <= X_r_eq_x)) (PreH11 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ”
.

Definition sm2n_mong_mul_partial_solve_wit_4_r_eq_x_aux := 
forall (result_pre: Z) (y_pre: Z) (x_pre: Z) (Y_r_eq_x: Z) (X_r_eq_x: Z) (PreH1 : ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH2 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH3 : ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD ))) (PreH4 : (0 <= (Y_r_eq_x * X_r_eq_x ))) (PreH5 : (0 <= (X_r_eq_x * Y_r_eq_x ))) (PreH6 : ((X_r_eq_x * Y_r_eq_x ) < U512_MOD)) (PreH7 : (Y_r_eq_x < SM2_N_Z)) (PreH8 : (0 <= Y_r_eq_x)) (PreH9 : (X_r_eq_x < SM2_N_Z)) (PreH10 : (0 <= X_r_eq_x)) (PreH11 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
|--
  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((Y_r_eq_x * X_r_eq_x ) < (SM2_N_Z * U256_MOD )) ” 
  &&  “ (0 <= (Y_r_eq_x * X_r_eq_x )) ” 
  &&  “ (0 <= (X_r_eq_x * Y_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * Y_r_eq_x ) < U512_MOD) ” 
  &&  “ (Y_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= Y_r_eq_x) ” 
  &&  “ (X_r_eq_x < SM2_N_Z) ” 
  &&  “ (0 <= X_r_eq_x) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * Y_r_eq_x ) )
  **  ((((( &( "interim" ) ) + (0 * sizeof(UINT64))) + (8 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_n )
  **  (store_sm2_rhon )
  **  (store_sm2_neg_inv_n )
  **  (store_u256_limbs (&((y_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) Y_r_eq_x )
.

Definition sm2n_mong_mul_partial_solve_wit_4_r_eq_x := sm2n_mong_mul_partial_solve_wit_4_r_eq_x_pure -> sm2n_mong_mul_partial_solve_wit_4_r_eq_x_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include basicop_facts_Strategy_Correct.

Axiom proof_of_sm2n_mong_mul_safety_wit_1_non_alias : sm2n_mong_mul_safety_wit_1_non_alias.
Axiom proof_of_sm2n_mong_mul_safety_wit_2_non_alias : sm2n_mong_mul_safety_wit_2_non_alias.
Axiom proof_of_sm2n_mong_mul_safety_wit_3_non_alias : sm2n_mong_mul_safety_wit_3_non_alias.
Axiom proof_of_sm2n_mong_mul_safety_wit_4_r_eq_x : sm2n_mong_mul_safety_wit_4_r_eq_x.
Axiom proof_of_sm2n_mong_mul_safety_wit_5_r_eq_x : sm2n_mong_mul_safety_wit_5_r_eq_x.
Axiom proof_of_sm2n_mong_mul_safety_wit_6_r_eq_x : sm2n_mong_mul_safety_wit_6_r_eq_x.
Axiom proof_of_sm2n_mong_mul_safety_wit_7_non_alias : sm2n_mong_mul_safety_wit_7_non_alias.
Axiom proof_of_sm2n_mong_mul_safety_wit_8_r_eq_x : sm2n_mong_mul_safety_wit_8_r_eq_x.
Axiom proof_of_sm2n_mong_mul_entail_wit_1_1_r_eq_x : sm2n_mong_mul_entail_wit_1_1_r_eq_x.
Axiom proof_of_sm2n_mong_mul_entail_wit_1_2_non_alias : sm2n_mong_mul_entail_wit_1_2_non_alias.
Axiom proof_of_sm2n_mong_mul_entail_wit_2_1_non_alias : sm2n_mong_mul_entail_wit_2_1_non_alias.
Axiom proof_of_sm2n_mong_mul_entail_wit_2_2_r_eq_x : sm2n_mong_mul_entail_wit_2_2_r_eq_x.
Axiom proof_of_sm2n_mong_mul_entail_wit_3_1_non_alias : sm2n_mong_mul_entail_wit_3_1_non_alias.
Axiom proof_of_sm2n_mong_mul_entail_wit_3_2_r_eq_x : sm2n_mong_mul_entail_wit_3_2_r_eq_x.
Axiom proof_of_sm2n_mong_mul_return_wit_1_non_alias : sm2n_mong_mul_return_wit_1_non_alias.
Axiom proof_of_sm2n_mong_mul_return_wit_2_r_eq_x : sm2n_mong_mul_return_wit_2_r_eq_x.
Axiom proof_of_sm2n_mong_mul_partial_solve_wit_1_non_alias : sm2n_mong_mul_partial_solve_wit_1_non_alias.
Axiom proof_of_sm2n_mong_mul_partial_solve_wit_2_r_eq_x : sm2n_mong_mul_partial_solve_wit_2_r_eq_x.
Axiom proof_of_sm2n_mong_mul_partial_solve_wit_3_non_alias_pure : sm2n_mong_mul_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_sm2n_mong_mul_partial_solve_wit_3_non_alias : sm2n_mong_mul_partial_solve_wit_3_non_alias.
Axiom proof_of_sm2n_mong_mul_partial_solve_wit_4_r_eq_x_pure : sm2n_mong_mul_partial_solve_wit_4_r_eq_x_pure.
Axiom proof_of_sm2n_mong_mul_partial_solve_wit_4_r_eq_x : sm2n_mong_mul_partial_solve_wit_4_r_eq_x.

End VC_Correct.
