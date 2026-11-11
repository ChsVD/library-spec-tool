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

(*----- Function pow_mod_p -----*)

Definition pow_mod_p_safety_wit_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition pow_mod_p_safety_wit_2_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition pow_mod_p_safety_wit_3_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pow_mod_p_safety_wit_4_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pow_mod_p_safety_wit_5_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= (X_non_alias * X_non_alias ))) (PreH2 : ((X_non_alias * X_non_alias ) < U512_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (X_non_alias <> 1)) (PreH7 : (X_non_alias < SM2_P_Z)) (PreH8 : (0 <= X_non_alias)) (PreH9 : (retval = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition pow_mod_p_entail_wit_1_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_2 = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_2_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_2_2_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval_2 <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_non_alias = 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval <> 0) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_3_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X_non_alias = 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval <> 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias = 1) ”
  &&  (store_fp x_pre X_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_4_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (PreH1 : (X_non_alias = 1)) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fp x_pre X_non_alias )
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_5_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (PreH1 : (X_non_alias < SM2_P_Z)) (PreH2 : (0 <= X_non_alias)) (PreH3 : (X_non_alias = 1)) ,
  (store_u256 x_pre X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UndefStructPredu32 result_pre )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_entail_wit_6_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (K: Z) (Zout: Z) (PreH1 : (0 <= Zout)) (PreH2 : (Zout < SM2_P_Z)) (PreH3 : ((X_non_alias * X_non_alias ) = (Zout + (K * SM2_P_Z ) ))) (PreH4 : (0 <= (X_non_alias * X_non_alias ))) (PreH5 : ((X_non_alias * X_non_alias ) < U512_MOD)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (X_non_alias <> 1)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (retval = 0)) ,
  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  EX (xs: (@list Z)) ,
  “ ((u64_list_value (xs)) = (X_non_alias * X_non_alias )) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 8) ” 
  &&  “ (0 <= Zout) ” 
  &&  “ (Zout < SM2_P_Z) ” 
  &&  “ ((X_non_alias * X_non_alias ) = (Zout + (K * SM2_P_Z ) )) ” 
  &&  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (UInt64Array.full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 xs )
  **  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition pow_mod_p_return_wit_1_non_alias := 
(
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  (UInt64Array.full &((result_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_fp x_pre X_non_alias )
  **  (store_fp result_pre (Zmod ((X_non_alias * X_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  TT && emp 
|--
  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = 1) ” 
  &&  “ (0 <= (Zmod ((1 * 1 )) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((1 * 1 )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((1 * 1 )) (SM2_P_Z))) ”
  &&  emp
).

Definition pow_mod_p_return_wit_1_non_alias_split_goal_1 := 
forall (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = 1)
.

Definition pow_mod_p_return_wit_1_non_alias_split_goal_2 := 
forall (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  (0 <= (Zmod ((1 * 1 )) (SM2_P_Z)))
.

Definition pow_mod_p_return_wit_1_non_alias_split_goal_3 := 
forall (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  ((Zmod ((1 * 1 )) (SM2_P_Z)) < SM2_P_Z)
.

Definition pow_mod_p_return_wit_1_non_alias_split_goal_4 := 
forall (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  ((u64_list_value ((cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))))) = (Zmod ((1 * 1 )) (SM2_P_Z)))
.

Definition pow_mod_p_return_wit_2_non_alias := 
(
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_non_alias * X_non_alias ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_non_alias * X_non_alias ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_non_alias * X_non_alias ))) (PreH8 : ((X_non_alias * X_non_alias ) < U512_MOD)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : (X_non_alias <> 1)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (retval = 0)) ,
  (store_fp result_pre Zout )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
|--
  (store_fp x_pre X_non_alias )
  **  (store_fp result_pre (Zmod ((X_non_alias * X_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (x_pre: Z) (X_non_alias: Z) (retval: Z) (K: Z) (Zout: Z) (xs: (@list Z)) (PreH1 : ((u64_list_value (xs)) = (X_non_alias * X_non_alias ))) (PreH2 : (u64_list_bounded xs )) (PreH3 : ((Zlength (xs)) = 8)) (PreH4 : (0 <= Zout)) (PreH5 : (Zout < SM2_P_Z)) (PreH6 : ((X_non_alias * X_non_alias ) = (Zout + (K * SM2_P_Z ) ))) (PreH7 : (0 <= (X_non_alias * X_non_alias ))) (PreH8 : ((X_non_alias * X_non_alias ) < U512_MOD)) (PreH9 : (0 <= retval)) (PreH10 : (retval <= 1)) (PreH11 : (retval = 0)) (PreH12 : (X_non_alias <> 1)) (PreH13 : (X_non_alias < SM2_P_Z)) (PreH14 : (0 <= X_non_alias)) (PreH15 : (retval = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
|--
  EX (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Zout = (Zmod ((X_non_alias * X_non_alias )) (SM2_P_Z))) ”
  &&  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition pow_mod_p_partial_solve_wit_1_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) ,
  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_fp x_pre X_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ”
  &&  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_partial_solve_wit_2_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (x0: Z) (x1: Z) (x2: Z) (x3: Z) (PreH1 : (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3)))) (PreH2 : (x3 < U64_MOD)) (PreH3 : (0 <= x3)) (PreH4 : (x2 < U64_MOD)) (PreH5 : (0 <= x2)) (PreH6 : (x1 < U64_MOD)) (PreH7 : (0 <= x1)) (PreH8 : (x0 < U64_MOD)) (PreH9 : (0 <= x0)) (PreH10 : (X_non_alias < SM2_P_Z)) (PreH11 : (0 <= X_non_alias)) (PreH12 : (X_non_alias = 1)) ,
  (UndefStructPredu32 result_pre )
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (X_non_alias = (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (X_non_alias = 1) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (UInt64Array.full &((x_pre)  # "u32" ->ₛ "v") 4 (cons (x0) ((cons (x1) ((cons (x2) ((cons (x3) ((@nil Z))))))))) )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_partial_solve_wit_3_non_alias := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X_non_alias <> 1)) (PreH5 : (X_non_alias < SM2_P_Z)) (PreH6 : (0 <= X_non_alias)) (PreH7 : (retval = 0)) ,
  (store_u256 x_pre X_non_alias )
  **  (UInt64Array.undef_full ( &( "res" ) ) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (UInt64Array.undef_full (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition pow_mod_p_partial_solve_wit_4_non_alias_pure := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= (X_non_alias * X_non_alias ))) (PreH2 : ((X_non_alias * X_non_alias ) < U512_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (X_non_alias <> 1)) (PreH7 : (X_non_alias < SM2_P_Z)) (PreH8 : (0 <= X_non_alias)) (PreH9 : (retval = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ”
.

Definition pow_mod_p_partial_solve_wit_4_non_alias_aux := 
forall (result_pre: Z) (x_pre: Z) (X_non_alias: Z) (retval: Z) (PreH1 : (0 <= (X_non_alias * X_non_alias ))) (PreH2 : ((X_non_alias * X_non_alias ) < U512_MOD)) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (X_non_alias <> 1)) (PreH7 : (X_non_alias < SM2_P_Z)) (PreH8 : (0 <= X_non_alias)) (PreH9 : (retval = 0)) ,
  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
  **  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= (X_non_alias * X_non_alias )) ” 
  &&  “ ((X_non_alias * X_non_alias ) < U512_MOD) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_non_alias <> 1) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (retval = 0) ”
  &&  (store_u64_limbs (( &( "res" ) ) + (0 * sizeof(UINT64))) 8 (X_non_alias * X_non_alias ) )
  **  (UInt64Array.undef_full &((result_pre)  # "u32" ->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_u256_limbs (&((x_pre)  # "u32" ->ₛ "v") + (0 * sizeof(UINT64))) X_non_alias )
.

Definition pow_mod_p_partial_solve_wit_4_non_alias := pow_mod_p_partial_solve_wit_4_non_alias_pure -> pow_mod_p_partial_solve_wit_4_non_alias_aux.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.

Axiom proof_of_pow_mod_p_safety_wit_1_non_alias : pow_mod_p_safety_wit_1_non_alias.
Axiom proof_of_pow_mod_p_safety_wit_2_non_alias : pow_mod_p_safety_wit_2_non_alias.
Axiom proof_of_pow_mod_p_safety_wit_3_non_alias : pow_mod_p_safety_wit_3_non_alias.
Axiom proof_of_pow_mod_p_safety_wit_4_non_alias : pow_mod_p_safety_wit_4_non_alias.
Axiom proof_of_pow_mod_p_safety_wit_5_non_alias : pow_mod_p_safety_wit_5_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_1_1_non_alias : pow_mod_p_entail_wit_1_1_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_1_2_non_alias : pow_mod_p_entail_wit_1_2_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_2_1_non_alias : pow_mod_p_entail_wit_2_1_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_2_2_non_alias : pow_mod_p_entail_wit_2_2_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_3_non_alias : pow_mod_p_entail_wit_3_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_4_non_alias : pow_mod_p_entail_wit_4_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_5_non_alias : pow_mod_p_entail_wit_5_non_alias.
Axiom proof_of_pow_mod_p_entail_wit_6_non_alias : pow_mod_p_entail_wit_6_non_alias.
Axiom proof_of_pow_mod_p_return_wit_1_non_alias : pow_mod_p_return_wit_1_non_alias.
Axiom proof_of_pow_mod_p_return_wit_2_non_alias : pow_mod_p_return_wit_2_non_alias.
Axiom proof_of_pow_mod_p_partial_solve_wit_1_non_alias : pow_mod_p_partial_solve_wit_1_non_alias.
Axiom proof_of_pow_mod_p_partial_solve_wit_2_non_alias : pow_mod_p_partial_solve_wit_2_non_alias.
Axiom proof_of_pow_mod_p_partial_solve_wit_3_non_alias : pow_mod_p_partial_solve_wit_3_non_alias.
Axiom proof_of_pow_mod_p_partial_solve_wit_4_non_alias_pure : pow_mod_p_partial_solve_wit_4_non_alias_pure.
Axiom proof_of_pow_mod_p_partial_solve_wit_4_non_alias : pow_mod_p_partial_solve_wit_4_non_alias.

End VC_Correct.
