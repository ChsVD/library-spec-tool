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
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.

(*----- Function AFPoint_neg -----*)

Definition AFPoint_neg_entail_wit_1 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias <> 0)) ,
  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
|--
  “ (Y_non_alias <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_sm2_p )
.

Definition AFPoint_neg_entail_wit_2 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (PreH1 : (Y_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_sm2_p )
|--
  EX (ys: (@list Z))  (xs: (@list Z)) ,
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "x") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
.

Definition AFPoint_neg_entail_wit_3 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (Y_non_alias <> 0)) ,
  (UInt64Array.full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
.

Definition AFPoint_neg_return_wit_1 := 
(
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) - (u64_list_value (ys)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u64_list_value (ys)) = Y_non_alias)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (Y_non_alias < SM2_P_Z)) (PreH10 : (0 <= Y_non_alias)) (PreH11 : ((u64_list_value (xs)) = X_non_alias)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (X_non_alias < SM2_P_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (Y_non_alias <> 0)) ,
  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") (u64_list_value (ys)) )
  **  (store_u256 &((result_pre)  # "AFPoint" ->ₛ "y") S )
  **  (UInt64Array.full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
|--
  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_afpoint_fields result_pre X_non_alias (Zmod ((-Y_non_alias)) (SM2_P_Z)) )
  **  (store_sm2_p )
) \/
(
forall (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) - (u64_list_value (ys)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u64_list_value (ys)) = Y_non_alias)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (Y_non_alias < SM2_P_Z)) (PreH10 : (0 <= Y_non_alias)) (PreH11 : ((u64_list_value (xs)) = X_non_alias)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (X_non_alias < SM2_P_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (Y_non_alias <> 0)) ,
  TT && emp 
|--
  “ (0 <= (Zmod ((-Y_non_alias)) (SM2_P_Z))) ” 
  &&  “ ((Zmod ((-Y_non_alias)) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (S = (Zmod ((-Y_non_alias)) (SM2_P_Z))) ” 
  &&  “ ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z) ”
  &&  emp
).

Definition AFPoint_neg_return_wit_1_split_goal_1 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) - (u64_list_value (ys)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u64_list_value (ys)) = Y_non_alias)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (Y_non_alias < SM2_P_Z)) (PreH10 : (0 <= Y_non_alias)) (PreH11 : ((u64_list_value (xs)) = X_non_alias)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (X_non_alias < SM2_P_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (Y_non_alias <> 0)) ,
  (0 <= (Zmod ((-Y_non_alias)) (SM2_P_Z)))
.

Definition AFPoint_neg_return_wit_1_split_goal_2 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) - (u64_list_value (ys)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u64_list_value (ys)) = Y_non_alias)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (Y_non_alias < SM2_P_Z)) (PreH10 : (0 <= Y_non_alias)) (PreH11 : ((u64_list_value (xs)) = X_non_alias)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (X_non_alias < SM2_P_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (Y_non_alias <> 0)) ,
  ((Zmod ((-Y_non_alias)) (SM2_P_Z)) < SM2_P_Z)
.

Definition AFPoint_neg_return_wit_1_split_goal_3 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) - (u64_list_value (ys)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u64_list_value (ys)) = Y_non_alias)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (Y_non_alias < SM2_P_Z)) (PreH10 : (0 <= Y_non_alias)) (PreH11 : ((u64_list_value (xs)) = X_non_alias)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (X_non_alias < SM2_P_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (Y_non_alias <> 0)) ,
  (S = (Zmod ((-Y_non_alias)) (SM2_P_Z)))
.

Definition AFPoint_neg_return_wit_1_split_goal_4 := 
forall (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (borrow: Z) (S: Z) (PreH1 : (0 <= S)) (PreH2 : (S < U256_MOD)) (PreH3 : (0 <= borrow)) (PreH4 : (borrow <= 1)) (PreH5 : (((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) - (u64_list_value (ys)) ) = (S - (borrow * U256_MOD ) ))) (PreH6 : ((u64_list_value (ys)) = Y_non_alias)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (Y_non_alias < SM2_P_Z)) (PreH10 : (0 <= Y_non_alias)) (PreH11 : ((u64_list_value (xs)) = X_non_alias)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (X_non_alias < SM2_P_Z)) (PreH15 : (0 <= X_non_alias)) (PreH16 : (Y_non_alias <> 0)) ,
  ((u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) = SM2_P_Z)
.

Definition AFPoint_neg_partial_solve_wit_1 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (Y_non_alias <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "x") )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  (store_sm2_p )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
  **  (store_sm2_p )
.

Definition AFPoint_neg_partial_solve_wit_2 := 
forall (result_pre: Z) (point_pre: Z) (Y_non_alias: Z) (X_non_alias: Z) (xs: (@list Z)) (ys: (@list Z)) (PreH1 : ((u64_list_value (ys)) = Y_non_alias)) (PreH2 : (u64_list_bounded ys )) (PreH3 : ((Zlength (ys)) = 4)) (PreH4 : (Y_non_alias < SM2_P_Z)) (PreH5 : (0 <= Y_non_alias)) (PreH6 : ((u64_list_value (xs)) = X_non_alias)) (PreH7 : (u64_list_bounded xs )) (PreH8 : ((Zlength (xs)) = 4)) (PreH9 : (X_non_alias < SM2_P_Z)) (PreH10 : (0 <= X_non_alias)) (PreH11 : (Y_non_alias <> 0)) ,
  (UInt64Array.full &(( &( "SM2_P" ) )->ₛ "v") 4 (cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))) )
  **  (UInt64Array.full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UndefStructPredu32 &((result_pre)  # "AFPoint" ->ₛ "y") )
|--
  “ ((u64_list_value (ys)) = Y_non_alias) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (Y_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= Y_non_alias) ” 
  &&  “ ((u64_list_value (xs)) = X_non_alias) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (X_non_alias < SM2_P_Z) ” 
  &&  “ (0 <= X_non_alias) ” 
  &&  “ (Y_non_alias <> 0) ”
  &&  (store_u256 ( &( "SM2_P" ) ) (u64_list_value ((cons (SM2_P_LIMB_0) ((cons (SM2_P_LIMB_1) ((cons (SM2_P_LIMB_2) ((cons (SM2_P_LIMB_3) ((@nil Z))))))))))) )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") (u64_list_value (ys)) )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((point_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 xs )
.

Definition AFPoint_neg_derive_mont_point_non_alias_by_non_alias := 
forall (result_pre: Z) (point_pre: Z) (P_mont_point_non_alias: ec_point) ,
  “ (P_mont_point_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint point_pre P_mont_point_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) ,
  (“ (Y_non_alias <> 0) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p ))
  **
  (((store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_afpoint_fields result_pre X_non_alias (Zmod ((-Y_non_alias)) (SM2_P_Z)) )
  **  (store_sm2_p ))
  -*
  ((store_mont_afpoint point_pre P_mont_point_non_alias )
  **  (store_mont_afpoint result_pre (sm2_point_negate (P_mont_point_non_alias)) )
  **  (store_sm2_p )))
.

Definition AFPoint_neg_derive_point_non_alias_by_non_alias := 
forall (result_pre: Z) (point_pre: Z) (P_point_non_alias: ec_point) ,
  “ (P_point_non_alias <> ECInfinity) ”
  &&  (store_afpoint point_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) ,
  (“ (Y_non_alias <> 0) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "AFPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p ))
  **
  (((store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_afpoint_fields result_pre X_non_alias (Zmod ((-Y_non_alias)) (SM2_P_Z)) )
  **  (store_sm2_p ))
  -*
  ((store_afpoint point_pre P_point_non_alias )
  **  (store_afpoint result_pre (sm2_point_negate (P_point_non_alias)) )
  **  (store_sm2_p )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.

Axiom proof_of_AFPoint_neg_entail_wit_1 : AFPoint_neg_entail_wit_1.
Axiom proof_of_AFPoint_neg_entail_wit_2 : AFPoint_neg_entail_wit_2.
Axiom proof_of_AFPoint_neg_entail_wit_3 : AFPoint_neg_entail_wit_3.
Axiom proof_of_AFPoint_neg_return_wit_1 : AFPoint_neg_return_wit_1.
Axiom proof_of_AFPoint_neg_partial_solve_wit_1 : AFPoint_neg_partial_solve_wit_1.
Axiom proof_of_AFPoint_neg_partial_solve_wit_2 : AFPoint_neg_partial_solve_wit_2.
Axiom proof_of_AFPoint_neg_derive_mont_point_non_alias_by_non_alias : AFPoint_neg_derive_mont_point_non_alias_by_non_alias.
Axiom proof_of_AFPoint_neg_derive_point_non_alias_by_non_alias : AFPoint_neg_derive_point_non_alias_by_non_alias.

End VC_Correct.
