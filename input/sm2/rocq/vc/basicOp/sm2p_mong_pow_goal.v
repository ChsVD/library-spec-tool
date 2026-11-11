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

(*----- Function sm2p_mong_pow -----*)

Definition sm2p_mong_pow_safety_wit_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2p_mong_pow_safety_wit_2_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2p_mong_pow_safety_wit_3_r_eq_x := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (PreH1 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2p_mong_pow_safety_wit_4_r_eq_x := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (PreH1 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2p_mong_pow_safety_wit_5_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (PreH1 : (0 <= (X_non_alias * X_non_alias ))) (PreH2 : ((X_non_alias * X_non_alias ) < U512_MOD)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2p_mong_pow_safety_wit_6_r_eq_x := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (PreH1 : (0 <= (X_r_eq_x * X_r_eq_x ))) (PreH2 : ((X_r_eq_x * X_r_eq_x ) < U512_MOD)) (PreH3 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * X_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sm2p_mong_pow_entail_wit_1_1_r_eq_x := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (X_r_eq_x: Z) (PreH1 : (result_pre = x_pre)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (result_pre = x_pre) ”
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition sm2p_mong_pow_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (X_r_eq_x: Z) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (result_pre = x_pre) ”
  &&  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition sm2p_mong_pow_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (X_r_eq_x: Z) (K: Z) (Zout: Z) (PreH1 : (0 <= Zout)) (PreH2 : (Zout < SM2_P_Z)) (PreH3 : ((Zout * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K * SM2_P_Z ) ))) (PreH4 : (0 <= (X_non_alias * X_non_alias ))) (PreH5 : ((X_non_alias * X_non_alias ) < U512_MOD)) ,
  (UInt64Array.full_shape (( &( "interim" ) ) + (0 * sizeof(UINT64))) 9 )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (K_2: Z)  (Zout_2: Z) ,
  “ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((Zout_2 * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K_2 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_x * X_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * X_r_eq_x ) < U512_MOD) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sm2p_mong_pow_entail_wit_2_2_r_eq_x := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (X_r_eq_x: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K_2 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_r_eq_x * X_r_eq_x ))) (PreH5 : ((X_r_eq_x * X_r_eq_x ) < U512_MOD)) (PreH6 : (result_pre = x_pre)) ,
  (UInt64Array.full_shape (( &( "interim" ) ) + (0 * sizeof(UINT64))) 9 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (K: Z)  (Zout: Z) ,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((Zout_2 * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K_2 * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_r_eq_x * X_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * X_r_eq_x ) < U512_MOD) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (UInt64Array.full_shape ( &( "interim" ) ) 9 )
  **  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition sm2p_mong_pow_return_wit_1_non_alias := 
(
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K_2 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_non_alias * X_non_alias ))) (PreH5 : ((X_non_alias * X_non_alias ) < U512_MOD)) ,
  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K * SM2_P_Z ) )) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (x_pre: Z) (X_non_alias: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K_2 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_non_alias * X_non_alias ))) (PreH5 : ((X_non_alias * X_non_alias ) < U512_MOD)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z)  (K: Z) ,
  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (0 <= Zout_2) ” 
  &&  “ (Zout_2 < SM2_P_Z) ” 
  &&  “ ((Zout_2 * U256_MOD ) = ((X_non_alias * X_non_alias ) + (K * SM2_P_Z ) )) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition sm2p_mong_pow_return_wit_2_r_eq_x := 
(
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K_2 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_r_eq_x * X_r_eq_x ))) (PreH5 : ((X_r_eq_x * X_r_eq_x ) < U512_MOD)) (PreH6 : (result_pre = x_pre)) ,
  (store_fp result_pre Zout_2 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (K: Z)  (Zout: Z) ,
  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((Zout * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K * SM2_P_Z ) )) ”
  &&  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (K_2: Z) (Zout_2: Z) (PreH1 : (0 <= Zout_2)) (PreH2 : (Zout_2 < SM2_P_Z)) (PreH3 : ((Zout_2 * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K_2 * SM2_P_Z ) ))) (PreH4 : (0 <= (X_r_eq_x * X_r_eq_x ))) (PreH5 : ((X_r_eq_x * X_r_eq_x ) < U512_MOD)) (PreH6 : (result_pre = x_pre)) ,
  TT && emp 
|--
  EX (K: Z) ,
  “ ((Zout_2 * U256_MOD ) = ((X_r_eq_x * X_r_eq_x ) + (K * SM2_P_Z ) )) ”
  &&  emp
).

Definition sm2p_mong_pow_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (UInt64Array.undef_full (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition sm2p_mong_pow_partial_solve_wit_2_r_eq_x := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (PreH1 : (result_pre = x_pre)) ,
  (UInt64Array.full ( &( "interim" ) ) 9 (repeat_Z (0) (9)) )
  **  (store_u256 x_pre X_r_eq_x )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = x_pre) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (UInt64Array.undef_full (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition sm2p_mong_pow_partial_solve_wit_3_non_alias_pure := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (PreH1 : (0 <= (X_non_alias * X_non_alias ))) (PreH2 : ((X_non_alias * X_non_alias ) < U512_MOD)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ”
.

Definition sm2p_mong_pow_partial_solve_wit_3_non_alias_aux := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (PreH1 : (0 <= (X_non_alias * X_non_alias ))) (PreH2 : ((X_non_alias * X_non_alias ) < U512_MOD)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ”
  &&  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  ((((( &( "interim" ) ) + (0 * sizeof(UINT64))) + (8 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
.

Definition sm2p_mong_pow_partial_solve_wit_3_non_alias := sm2p_mong_pow_partial_solve_wit_3_non_alias_pure -> sm2p_mong_pow_partial_solve_wit_3_non_alias_aux.

Definition sm2p_mong_pow_partial_solve_wit_4_r_eq_x_pure := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (PreH1 : (0 <= (X_r_eq_x * X_r_eq_x ))) (PreH2 : ((X_r_eq_x * X_r_eq_x ) < U512_MOD)) (PreH3 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * X_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_r_eq_x * X_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * X_r_eq_x ) < U512_MOD) ”
.

Definition sm2p_mong_pow_partial_solve_wit_4_r_eq_x_aux := 
forall (result_pre: Z) (x_pre: Z) (X_r_eq_x: Z) (PreH1 : (0 <= (X_r_eq_x * X_r_eq_x ))) (PreH2 : ((X_r_eq_x * X_r_eq_x ) < U512_MOD)) (PreH3 : (result_pre = x_pre)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_r_eq_x )
  **  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * X_r_eq_x ) )
  **  (UInt64Array.full (( &( "interim" ) ) + (8 * sizeof(UINT64))) (9 - 8 ) (repeat_Z (0) ((9 - 8 ))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_r_eq_x * X_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * X_r_eq_x ) < U512_MOD) ” 
  &&  “ (0 <= (X_r_eq_x * X_r_eq_x )) ” 
  &&  “ ((X_r_eq_x * X_r_eq_x ) < U512_MOD) ” 
  &&  “ (result_pre = x_pre) ”
  &&  (store_u64_limbs (( &( "interim" ) ) + (0 * sizeof(UINT64))) 8 (X_r_eq_x * X_r_eq_x ) )
  **  ((((( &( "interim" ) ) + (0 * sizeof(UINT64))) + (8 * sizeof(UINT64)))) # UInt64  |-> 0)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition sm2p_mong_pow_partial_solve_wit_4_r_eq_x := sm2p_mong_pow_partial_solve_wit_4_r_eq_x_pure -> sm2p_mong_pow_partial_solve_wit_4_r_eq_x_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_sm2p_mong_pow_safety_wit_1_non_alias : sm2p_mong_pow_safety_wit_1_non_alias.
Axiom proof_of_sm2p_mong_pow_safety_wit_2_non_alias : sm2p_mong_pow_safety_wit_2_non_alias.
Axiom proof_of_sm2p_mong_pow_safety_wit_3_r_eq_x : sm2p_mong_pow_safety_wit_3_r_eq_x.
Axiom proof_of_sm2p_mong_pow_safety_wit_4_r_eq_x : sm2p_mong_pow_safety_wit_4_r_eq_x.
Axiom proof_of_sm2p_mong_pow_safety_wit_5_non_alias : sm2p_mong_pow_safety_wit_5_non_alias.
Axiom proof_of_sm2p_mong_pow_safety_wit_6_r_eq_x : sm2p_mong_pow_safety_wit_6_r_eq_x.
Axiom proof_of_sm2p_mong_pow_entail_wit_1_1_r_eq_x : sm2p_mong_pow_entail_wit_1_1_r_eq_x.
Axiom proof_of_sm2p_mong_pow_entail_wit_1_2_non_alias : sm2p_mong_pow_entail_wit_1_2_non_alias.
Axiom proof_of_sm2p_mong_pow_entail_wit_2_1_non_alias : sm2p_mong_pow_entail_wit_2_1_non_alias.
Axiom proof_of_sm2p_mong_pow_entail_wit_2_2_r_eq_x : sm2p_mong_pow_entail_wit_2_2_r_eq_x.
Axiom proof_of_sm2p_mong_pow_return_wit_1_non_alias : sm2p_mong_pow_return_wit_1_non_alias.
Axiom proof_of_sm2p_mong_pow_return_wit_2_r_eq_x : sm2p_mong_pow_return_wit_2_r_eq_x.
Axiom proof_of_sm2p_mong_pow_partial_solve_wit_1_non_alias : sm2p_mong_pow_partial_solve_wit_1_non_alias.
Axiom proof_of_sm2p_mong_pow_partial_solve_wit_2_r_eq_x : sm2p_mong_pow_partial_solve_wit_2_r_eq_x.
Axiom proof_of_sm2p_mong_pow_partial_solve_wit_3_non_alias_pure : sm2p_mong_pow_partial_solve_wit_3_non_alias_pure.
Axiom proof_of_sm2p_mong_pow_partial_solve_wit_3_non_alias : sm2p_mong_pow_partial_solve_wit_3_non_alias.
Axiom proof_of_sm2p_mong_pow_partial_solve_wit_4_r_eq_x_pure : sm2p_mong_pow_partial_solve_wit_4_r_eq_x_pure.
Axiom proof_of_sm2p_mong_pow_partial_solve_wit_4_r_eq_x : sm2p_mong_pow_partial_solve_wit_4_r_eq_x.

End VC_Correct.
