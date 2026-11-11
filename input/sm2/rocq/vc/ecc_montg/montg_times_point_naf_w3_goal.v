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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_overwrite_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_precomp_points_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_precomp_points_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_predicate_cancellation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import wnaf3_predicate_cancellation_strategy_proof.

(*----- Function montg_times_point_naf_w3 -----*)

Definition montg_times_point_naf_w3_safety_wit_1_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_2_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "ki" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_3_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (wnaf3_precomp_undef ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_4_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (wnaf3_precomp_undef ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_5_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.undef_full ( &( "naf_k" ) ) 257 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_6_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (PreH1 : (wnaf3_representation K_non_alias digits )) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition montg_times_point_naf_w3_safety_wit_7_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH2 : (wnaf3_representation K_non_alias initial_digits )) (PreH3 : (wnaf3_digit first_digit )) (PreH4 : (wnaf3_representation K_non_alias digits )) (PreH5 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_8_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit > 0)) (PreH2 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH3 : (wnaf3_representation K_non_alias initial_digits )) (PreH4 : (wnaf3_digit first_digit )) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (first_digit * sizeof( "AFPoint" ))) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_9_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit <= 0)) (PreH2 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH3 : (wnaf3_representation K_non_alias initial_digits )) (PreH4 : (wnaf3_digit first_digit )) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_10_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit < 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit <> (INT_MIN)) ”
) \/
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit < 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit <> (INT_MIN)) ”
).

Definition montg_times_point_naf_w3_safety_wit_10_non_alias_split_goal_1 := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit < 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit <> (INT_MIN)) ”
.

Definition montg_times_point_naf_w3_safety_wit_11_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit < 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_12_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (digits_2: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (digits_2)))))) (PreH3 : (wnaf3_representation K_non_alias digits_2 )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH6 : ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH7 : (retval = 1)) (PreH8 : (first_digit > 0)) (PreH9 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH10 : (wnaf3_representation K_non_alias initial_digits )) (PreH11 : (wnaf3_digit first_digit )) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_2))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
|--
  “ (255 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 255) ”
.

Definition montg_times_point_naf_w3_safety_wit_13_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (digits_2: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (digits_2)))))) (PreH3 : (wnaf3_representation K_non_alias digits_2 )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH6 : ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH7 : (retval = 1)) (PreH8 : (first_digit < 0)) (PreH9 : (first_digit <= 0)) (PreH10 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH11 : (wnaf3_representation K_non_alias initial_digits )) (PreH12 : (wnaf3_digit first_digit )) (PreH13 : (wnaf3_representation K_non_alias digits )) (PreH14 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_2))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
|--
  “ (255 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 255) ”
.

Definition montg_times_point_naf_w3_safety_wit_14_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (digits_2: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (digits_2)))))) (PreH3 : (wnaf3_representation K_non_alias digits_2 )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH6 : (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH7 : (first_digit >= 0)) (PreH8 : (first_digit <= 0)) (PreH9 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH10 : (wnaf3_representation K_non_alias initial_digits )) (PreH11 : (wnaf3_digit first_digit )) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_2))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
|--
  “ (255 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 255) ”
.

Definition montg_times_point_naf_w3_safety_wit_15_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (Acc: ec_point) (digits: (@list Z)) (i: Z) (PreH1 : ((-1) <= i)) (PreH2 : (i <= 255)) (PreH3 : (0 <= K_non_alias)) (PreH4 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_16_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) (PreH5 : (wnaf3_digit digit )) (PreH6 : (i >= 0)) (PreH7 : ((-1) <= i)) (PreH8 : (i <= 255)) (PreH9 : (0 <= K_non_alias)) (PreH10 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH11 : (wnaf3_representation K_non_alias digits )) (PreH12 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH13 : (digit <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_17_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (digit * sizeof( "AFPoint" ))) (sm2_point_mul (digit) (BasePoint_non_alias)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_18_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (digit <> (INT_MIN)) ”
) \/
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (digit <> (INT_MIN)) ”
).

Definition montg_times_point_naf_w3_safety_wit_18_non_alias_split_goal_1 := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (digit <> (INT_MIN)) ”
.

Definition montg_times_point_naf_w3_safety_wit_19_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition montg_times_point_naf_w3_safety_wit_20_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias)))) (PreH3 : (digit > 0)) (PreH4 : (digit = (Znth (i) (digits) (0)))) (PreH5 : (0 <= i)) (PreH6 : (i < 256)) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (wnaf3_digit digit )) (PreH9 : (i >= 0)) (PreH10 : ((-1) <= i)) (PreH11 : (i <= 255)) (PreH12 : (0 <= K_non_alias)) (PreH13 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH14 : (wnaf3_representation K_non_alias digits )) (PreH15 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH16 : (digit <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition montg_times_point_naf_w3_safety_wit_21_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias)))) (PreH3 : (digit < 0)) (PreH4 : (i <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (digit <= 0)) (PreH7 : (digit = (Znth (i) (digits) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < 256)) (PreH10 : (wnaf3_representation K_non_alias digits )) (PreH11 : (wnaf3_digit digit )) (PreH12 : (i >= 0)) (PreH13 : ((-1) <= i)) (PreH14 : (i <= 255)) (PreH15 : (0 <= K_non_alias)) (PreH16 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH17 : (wnaf3_representation K_non_alias digits )) (PreH18 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH19 : (digit <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition montg_times_point_naf_w3_safety_wit_22_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits)))))) (PreH2 : ((sm2_point_double (Acc)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias)))) (PreH3 : (digit = (Znth (i) (digits) (0)))) (PreH4 : (0 <= i)) (PreH5 : (i < 256)) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (wnaf3_digit digit )) (PreH8 : (i >= 0)) (PreH9 : ((-1) <= i)) (PreH10 : (i <= 255)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH13 : (wnaf3_representation K_non_alias digits )) (PreH14 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH15 : (digit = 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition montg_times_point_naf_w3_entail_wit_1_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (StructAFPointArray.undef_full ( &( "PT" ) ) 4 )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (wnaf3_positive_array_undef ( &( "PT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_2_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (StructAFPointArray.undef_full ( &( "NT" ) ) 4 )
  **  (wnaf3_positive_array_undef ( &( "PT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (wnaf3_negative_array_undef ( &( "NT" ) ) )
  **  (wnaf3_positive_array_undef ( &( "PT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_3_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (wnaf3_negative_array_undef ( &( "NT" ) ) )
  **  (wnaf3_positive_array_undef ( &( "PT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (wnaf3_precomp_undef ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_4_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_mont_wnaf3_precomp (( &( "PT" ) ) + (0 * sizeof( "AFPoint" ))) (( &( "NT" ) ) + (0 * sizeof( "AFPoint" ))) BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_5_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (CharArray.undef_full ( &( "naf_k" ) ) 257 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_6_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_fn k_pre K_non_alias )
  **  (store_wnaf3 (( &( "naf_k" ) ) + (0 * sizeof(CHAR))) K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  EX (digits: (@list Z)) ,
  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (CharArray.full (( &( "naf_k" ) ) + (0 * sizeof(CHAR))) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_7_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (PreH1 : (wnaf3_representation K_non_alias digits )) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.full (( &( "naf_k" ) ) + (0 * sizeof(CHAR))) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_8_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit > 0)) (PreH2 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH3 : (wnaf3_representation K_non_alias initial_digits )) (PreH4 : (wnaf3_digit first_digit )) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit > 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (first_digit * sizeof( "AFPoint" ))) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_9_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit > 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_afpoint (( &( "PT" ) ) + (first_digit * sizeof( "AFPoint" ))) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (retval = 1) ” 
  &&  “ (first_digit > 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_10_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit > 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (first_digit > 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit > 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  TT && emp 
|--
  “ ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ (0 <= K_non_alias) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit > 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit > 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))
.

Definition montg_times_point_naf_w3_entail_wit_10_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit > 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (0 <= K_non_alias)
.

Definition montg_times_point_naf_w3_entail_wit_11_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit < 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit < 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_12_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit < 0)) (PreH3 : (first_digit <= 0)) (PreH4 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH5 : (wnaf3_representation K_non_alias initial_digits )) (PreH6 : (wnaf3_digit first_digit )) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (retval = 1) ” 
  &&  “ (first_digit < 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_entail_wit_13_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit < 0)) (PreH3 : (first_digit <= 0)) (PreH4 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH5 : (wnaf3_representation K_non_alias initial_digits )) (PreH6 : (wnaf3_digit first_digit )) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (first_digit < 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit < 0)) (PreH3 : (first_digit <= 0)) (PreH4 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH5 : (wnaf3_representation K_non_alias initial_digits )) (PreH6 : (wnaf3_digit first_digit )) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (BasePoint_non_alias <> ECInfinity)) ,
  TT && emp 
|--
  “ ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ (0 <= K_non_alias) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit < 0)) (PreH3 : (first_digit <= 0)) (PreH4 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH5 : (wnaf3_representation K_non_alias initial_digits )) (PreH6 : (wnaf3_digit first_digit )) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (BasePoint_non_alias <> ECInfinity)) ,
  ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit < 0)) (PreH3 : (first_digit <= 0)) (PreH4 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH5 : (wnaf3_representation K_non_alias initial_digits )) (PreH6 : (wnaf3_digit first_digit )) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (BasePoint_non_alias <> ECInfinity)) ,
  (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))
.

Definition montg_times_point_naf_w3_entail_wit_13_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (first_digit < 0)) (PreH3 : (first_digit <= 0)) (PreH4 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH5 : (wnaf3_representation K_non_alias initial_digits )) (PreH6 : (wnaf3_digit first_digit )) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (BasePoint_non_alias <> ECInfinity)) ,
  (0 <= K_non_alias)
.

Definition montg_times_point_naf_w3_entail_wit_14_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit >= 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (first_digit >= 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit >= 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  TT && emp 
|--
  “ (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ (0 <= K_non_alias) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit >= 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit >= 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))
.

Definition montg_times_point_naf_w3_entail_wit_14_non_alias_split_goal_3 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit >= 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (0 <= K_non_alias)
.

Definition montg_times_point_naf_w3_entail_wit_15_1_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH3 : ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH4 : (retval = 1)) (PreH5 : (first_digit > 0)) (PreH6 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH7 : (wnaf3_representation K_non_alias initial_digits )) (PreH8 : (wnaf3_digit first_digit )) (PreH9 : (wnaf3_representation K_non_alias digits )) (PreH10 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  EX (digits_2: (@list Z)) ,
  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (digits_2))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits_2 ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (first_digit > 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_2))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
.

Definition montg_times_point_naf_w3_entail_wit_15_2_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval_2: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH3 : ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH4 : (retval_2 = 1)) (PreH5 : (first_digit < 0)) (PreH6 : (first_digit <= 0)) (PreH7 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH8 : (wnaf3_representation K_non_alias initial_digits )) (PreH9 : (wnaf3_digit first_digit )) (PreH10 : (wnaf3_representation K_non_alias digits )) (PreH11 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  EX (digits_3: (@list Z)) ,
  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (digits_3))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits_3 ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (first_digit < 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_3))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_3 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
.

Definition montg_times_point_naf_w3_entail_wit_15_3_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH3 : (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH4 : (first_digit >= 0)) (PreH5 : (first_digit <= 0)) (PreH6 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH7 : (wnaf3_representation K_non_alias initial_digits )) (PreH8 : (wnaf3_digit first_digit )) (PreH9 : (wnaf3_representation K_non_alias digits )) (PreH10 : (BasePoint_non_alias <> ECInfinity)) ,
  ((( &( "ki" ) )) # Char  |-> first_digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  EX (digits_4: (@list Z)) ,
  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (digits_4))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits_4 ) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits))))) ” 
  &&  “ (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias))) ” 
  &&  “ (first_digit >= 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_4))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_4 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
.

Definition montg_times_point_naf_w3_entail_wit_16_1_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits_2: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (digits_3: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (digits_3)))))) (PreH3 : (wnaf3_representation K_non_alias digits_3 )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH6 : ((sm2_point_mul (first_digit) (BasePoint_non_alias)) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH7 : (retval = 1)) (PreH8 : (first_digit > 0)) (PreH9 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH10 : (wnaf3_representation K_non_alias initial_digits )) (PreH11 : (wnaf3_digit first_digit )) (PreH12 : (wnaf3_representation K_non_alias digits_2 )) (PreH13 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_3))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_3 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (Acc: ec_point)  (digits: (@list Z)) ,
  “ ((-1) <= 255) ” 
  &&  “ (255 <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((255 + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((255 + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_16_2_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits_2: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (retval: Z) (digits_3: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (digits_3)))))) (PreH3 : (wnaf3_representation K_non_alias digits_3 )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH6 : ((sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH7 : (retval = 1)) (PreH8 : (first_digit < 0)) (PreH9 : (first_digit <= 0)) (PreH10 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH11 : (wnaf3_representation K_non_alias initial_digits )) (PreH12 : (wnaf3_digit first_digit )) (PreH13 : (wnaf3_representation K_non_alias digits_2 )) (PreH14 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_3))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_3 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (Acc: ec_point)  (digits: (@list Z)) ,
  “ ((-1) <= 255) ” 
  &&  “ (255 <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((255 + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((255 + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_16_3_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits_2: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (digits_3: (@list Z)) (PreH1 : (0 <= K_non_alias)) (PreH2 : (0 <= (wnaf3_value ((sublist (256) (257) (digits_3)))))) (PreH3 : (wnaf3_representation K_non_alias digits_3 )) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist (256) (257) (initial_digits)))))) (PreH6 : (ECInfinity = (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (initial_digits))))) (BasePoint_non_alias)))) (PreH7 : (first_digit >= 0)) (PreH8 : (first_digit <= 0)) (PreH9 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH10 : (wnaf3_representation K_non_alias initial_digits )) (PreH11 : (wnaf3_digit first_digit )) (PreH12 : (wnaf3_representation K_non_alias digits_2 )) (PreH13 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_mul ((wnaf3_value ((sublist (256) (257) (digits_3))))) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_3 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (Acc: ec_point)  (digits: (@list Z)) ,
  “ ((-1) <= 255) ” 
  &&  “ (255 <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((255 + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((255 + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_17_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (digit > 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (digit * sizeof( "AFPoint" ))) (sm2_point_mul (digit) (BasePoint_non_alias)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_18_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (( &( "Q" ) ) = ( &( "Q" ) ))) (PreH2 : (digit > 0)) (PreH3 : (digit = (Znth (i) (digits) (0)))) (PreH4 : (0 <= i)) (PreH5 : (i < 256)) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (wnaf3_digit digit )) (PreH8 : (i >= 0)) (PreH9 : ((-1) <= i)) (PreH10 : (i <= 255)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH13 : (wnaf3_representation K_non_alias digits )) (PreH14 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH15 : (digit <> 0)) ,
  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) )
  **  (store_mont_afpoint (( &( "PT" ) ) + (digit * sizeof( "AFPoint" ))) (sm2_point_mul (digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ” 
  &&  “ (digit > 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
.

Definition montg_times_point_naf_w3_entail_wit_19_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (( &( "Q" ) ) = ( &( "Q" ) ))) (PreH2 : (digit > 0)) (PreH3 : (digit = (Znth (i) (digits) (0)))) (PreH4 : (0 <= i)) (PreH5 : (i < 256)) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (wnaf3_digit digit )) (PreH8 : (i >= 0)) (PreH9 : ((-1) <= i)) (PreH10 : (i <= 255)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH13 : (wnaf3_representation K_non_alias digits )) (PreH14 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH15 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  “ (0 <= (wnaf3_value ((sublist (i) (257) (digits))))) ” 
  &&  “ ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit > 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  TT && emp 
|--
  “ ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (i) (257) (digits))))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_19_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_19_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  (0 <= (wnaf3_value ((sublist (i) (257) (digits)))))
.

Definition montg_times_point_naf_w3_entail_wit_20_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit <= 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (digit < 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (digit <= 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_21_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (digit < 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (digit <= 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_entail_wit_22_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (( &( "Q" ) ) = ( &( "Q" ) ))) (PreH2 : (digit < 0)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (digit <= 0)) (PreH6 : (digit = (Znth (i) (digits) (0)))) (PreH7 : (0 <= i)) (PreH8 : (i < 256)) (PreH9 : (wnaf3_representation K_non_alias digits )) (PreH10 : (wnaf3_digit digit )) (PreH11 : (i >= 0)) (PreH12 : ((-1) <= i)) (PreH13 : (i <= 255)) (PreH14 : (0 <= K_non_alias)) (PreH15 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH16 : (wnaf3_representation K_non_alias digits )) (PreH17 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH18 : (digit <> 0)) ,
  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ” 
  &&  “ (digit < 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (digit <= 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
.

Definition montg_times_point_naf_w3_entail_wit_23_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (( &( "Q" ) ) = ( &( "Q" ) ))) (PreH2 : (digit < 0)) (PreH3 : (i <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (digit <= 0)) (PreH6 : (digit = (Znth (i) (digits) (0)))) (PreH7 : (0 <= i)) (PreH8 : (i < 256)) (PreH9 : (wnaf3_representation K_non_alias digits )) (PreH10 : (wnaf3_digit digit )) (PreH11 : (i >= 0)) (PreH12 : ((-1) <= i)) (PreH13 : (i <= 255)) (PreH14 : (0 <= K_non_alias)) (PreH15 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH16 : (wnaf3_representation K_non_alias digits )) (PreH17 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH18 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  “ (0 <= (wnaf3_value ((sublist (i) (257) (digits))))) ” 
  &&  “ ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit < 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (digit <= 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  TT && emp 
|--
  “ ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (i) (257) (digits))))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_23_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  ((sm2_point_add ((sm2_point_double (Acc))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_23_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (0 <= (wnaf3_value ((sublist (i) (257) (digits)))))
.

Definition montg_times_point_naf_w3_entail_wit_24_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) (PreH5 : (wnaf3_digit digit )) (PreH6 : (i >= 0)) (PreH7 : ((-1) <= i)) (PreH8 : (i <= 255)) (PreH9 : (0 <= K_non_alias)) (PreH10 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH11 : (wnaf3_representation K_non_alias digits )) (PreH12 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH13 : (digit = 0)) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (0 <= (wnaf3_value ((sublist (i) (257) (digits))))) ” 
  &&  “ ((sm2_point_double (Acc)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit = 0) ”
  &&  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) (PreH5 : (wnaf3_digit digit )) (PreH6 : (i >= 0)) (PreH7 : ((-1) <= i)) (PreH8 : (i <= 255)) (PreH9 : (0 <= K_non_alias)) (PreH10 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH11 : (wnaf3_representation K_non_alias digits )) (PreH12 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH13 : (digit = 0)) ,
  TT && emp 
|--
  “ ((sm2_point_double (Acc)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (i) (257) (digits))))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_24_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) (PreH5 : (wnaf3_digit digit )) (PreH6 : (i >= 0)) (PreH7 : ((-1) <= i)) (PreH8 : (i <= 255)) (PreH9 : (0 <= K_non_alias)) (PreH10 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH11 : (wnaf3_representation K_non_alias digits )) (PreH12 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH13 : (digit = 0)) ,
  ((sm2_point_double (Acc)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits))))) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_24_non_alias_split_goal_2 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) (PreH5 : (wnaf3_digit digit )) (PreH6 : (i >= 0)) (PreH7 : ((-1) <= i)) (PreH8 : (i <= 255)) (PreH9 : (0 <= K_non_alias)) (PreH10 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH11 : (wnaf3_representation K_non_alias digits )) (PreH12 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH13 : (digit = 0)) ,
  (0 <= (wnaf3_value ((sublist (i) (257) (digits)))))
.

Definition montg_times_point_naf_w3_entail_wit_25_1_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit > 0)) (PreH4 : (digit = (Znth (i) (digits_2) (0)))) (PreH5 : (0 <= i)) (PreH6 : (i < 256)) (PreH7 : (wnaf3_representation K_non_alias digits_2 )) (PreH8 : (wnaf3_digit digit )) (PreH9 : (i >= 0)) (PreH10 : ((-1) <= i)) (PreH11 : (i <= 255)) (PreH12 : (0 <= K_non_alias)) (PreH13 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH14 : (wnaf3_representation K_non_alias digits_2 )) (PreH15 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH16 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  EX (Acc: ec_point)  (digits: (@list Z)) ,
  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit > 0)) (PreH4 : (digit = (Znth (i) (digits_2) (0)))) (PreH5 : (0 <= i)) (PreH6 : (i < 256)) (PreH7 : (wnaf3_representation K_non_alias digits_2 )) (PreH8 : (wnaf3_digit digit )) (PreH9 : (i >= 0)) (PreH10 : ((-1) <= i)) (PreH11 : (i <= 255)) (PreH12 : (0 <= K_non_alias)) (PreH13 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH14 : (wnaf3_representation K_non_alias digits_2 )) (PreH15 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH16 : (digit <> 0)) ,
  TT && emp 
|--
  “ (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits_2))))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_25_1_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_mul (digit) (BasePoint_non_alias)))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit > 0)) (PreH4 : (digit = (Znth (i) (digits_2) (0)))) (PreH5 : (0 <= i)) (PreH6 : (i < 256)) (PreH7 : (wnaf3_representation K_non_alias digits_2 )) (PreH8 : (wnaf3_digit digit )) (PreH9 : (i >= 0)) (PreH10 : ((-1) <= i)) (PreH11 : (i <= 255)) (PreH12 : (0 <= K_non_alias)) (PreH13 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH14 : (wnaf3_representation K_non_alias digits_2 )) (PreH15 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH16 : (digit <> 0)) ,
  (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits_2)))))
.

Definition montg_times_point_naf_w3_entail_wit_25_2_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit < 0)) (PreH4 : (i <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (digit <= 0)) (PreH7 : (digit = (Znth (i) (digits_2) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < 256)) (PreH10 : (wnaf3_representation K_non_alias digits_2 )) (PreH11 : (wnaf3_digit digit )) (PreH12 : (i >= 0)) (PreH13 : ((-1) <= i)) (PreH14 : (i <= 255)) (PreH15 : (0 <= K_non_alias)) (PreH16 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH17 : (wnaf3_representation K_non_alias digits_2 )) (PreH18 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH19 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
|--
  EX (Acc: ec_point)  (digits: (@list Z)) ,
  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit < 0)) (PreH4 : (i <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (digit <= 0)) (PreH7 : (digit = (Znth (i) (digits_2) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < 256)) (PreH10 : (wnaf3_representation K_non_alias digits_2 )) (PreH11 : (wnaf3_digit digit )) (PreH12 : (i >= 0)) (PreH13 : ((-1) <= i)) (PreH14 : (i <= 255)) (PreH15 : (0 <= K_non_alias)) (PreH16 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH17 : (wnaf3_representation K_non_alias digits_2 )) (PreH18 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH19 : (digit <> 0)) ,
  TT && emp 
|--
  “ (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits_2))))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_25_2_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_add ((sm2_point_double (Acc_2))) ((sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))))) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit < 0)) (PreH4 : (i <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : (digit <= 0)) (PreH7 : (digit = (Znth (i) (digits_2) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < 256)) (PreH10 : (wnaf3_representation K_non_alias digits_2 )) (PreH11 : (wnaf3_digit digit )) (PreH12 : (i >= 0)) (PreH13 : ((-1) <= i)) (PreH14 : (i <= 255)) (PreH15 : (0 <= K_non_alias)) (PreH16 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH17 : (wnaf3_representation K_non_alias digits_2 )) (PreH18 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH19 : (digit <> 0)) ,
  (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits_2)))))
.

Definition montg_times_point_naf_w3_entail_wit_25_3_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_double (Acc_2)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit = (Znth (i) (digits_2) (0)))) (PreH4 : (0 <= i)) (PreH5 : (i < 256)) (PreH6 : (wnaf3_representation K_non_alias digits_2 )) (PreH7 : (wnaf3_digit digit )) (PreH8 : (i >= 0)) (PreH9 : ((-1) <= i)) (PreH10 : (i <= 255)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH13 : (wnaf3_representation K_non_alias digits_2 )) (PreH14 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH15 : (digit = 0)) ,
  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits_2 )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc_2)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  EX (Acc: ec_point)  (digits: (@list Z)) ,
  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_double (Acc_2)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit = (Znth (i) (digits_2) (0)))) (PreH4 : (0 <= i)) (PreH5 : (i < 256)) (PreH6 : (wnaf3_representation K_non_alias digits_2 )) (PreH7 : (wnaf3_digit digit )) (PreH8 : (i >= 0)) (PreH9 : ((-1) <= i)) (PreH10 : (i <= 255)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH13 : (wnaf3_representation K_non_alias digits_2 )) (PreH14 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH15 : (digit = 0)) ,
  TT && emp 
|--
  “ (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits_2))))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_25_3_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits_2: (@list Z)) (Acc_2: ec_point) (digit: Z) (PreH1 : (0 <= (wnaf3_value ((sublist (i) (257) (digits_2)))))) (PreH2 : ((sm2_point_double (Acc_2)) = (sm2_point_mul ((wnaf3_value ((sublist (i) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH3 : (digit = (Znth (i) (digits_2) (0)))) (PreH4 : (0 <= i)) (PreH5 : (i < 256)) (PreH6 : (wnaf3_representation K_non_alias digits_2 )) (PreH7 : (wnaf3_digit digit )) (PreH8 : (i >= 0)) (PreH9 : ((-1) <= i)) (PreH10 : (i <= 255)) (PreH11 : (0 <= K_non_alias)) (PreH12 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits_2)))))) (PreH13 : (wnaf3_representation K_non_alias digits_2 )) (PreH14 : (Acc_2 = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits_2))))) (BasePoint_non_alias)))) (PreH15 : (digit = 0)) ,
  (0 <= (wnaf3_value ((sublist (((i - 1 ) + 1 )) (257) (digits_2)))))
.

Definition montg_times_point_naf_w3_entail_wit_26_non_alias := 
(
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i < 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias))) ” 
  &&  “ (i < 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
) \/
(
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i < 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  TT && emp 
|--
  “ (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias))) ”
  &&  emp
).

Definition montg_times_point_naf_w3_entail_wit_26_non_alias_split_goal_1 := 
forall (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i < 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias)))
.

Definition montg_times_point_naf_w3_entail_wit_27_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias)))) (PreH2 : (i < 0)) (PreH3 : ((-1) <= i)) (PreH4 : (i <= 255)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_jpoint result_pre Acc )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
|--
  “ (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias))) ” 
  &&  “ (i < 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (StructAFPointArray.undef_full ( &( "NT" ) ) 4 )
  **  (StructAFPointArray.undef_full ( &( "PT" ) ) 4 )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_jpoint result_pre Acc )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
.

Definition montg_times_point_naf_w3_return_wit_1_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias)))) (PreH2 : (i < 0)) (PreH3 : ((-1) <= i)) (PreH4 : (i <= 255)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (store_mont_jpoint result_pre Acc )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint result_pre (sm2_point_mul (K_non_alias) (BasePoint_non_alias)) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_partial_solve_wit_1_non_alias_pure := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (wnaf3_precomp_undef ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  ((( &( "ki" ) )) # Char  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
.

Definition montg_times_point_naf_w3_partial_solve_wit_1_non_alias_aux := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (wnaf3_precomp_undef ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (BasePoint_non_alias <> ECInfinity) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_afpoint P_pre BasePoint_non_alias )
  **  (wnaf3_precomp_undef (( &( "PT" ) ) + (0 * sizeof( "AFPoint" ))) (( &( "NT" ) ) + (0 * sizeof( "AFPoint" ))) )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 (repeat_Z (0) (257)) )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_1_non_alias := montg_times_point_naf_w3_partial_solve_wit_1_non_alias_pure -> montg_times_point_naf_w3_partial_solve_wit_1_non_alias_aux.

Definition montg_times_point_naf_w3_partial_solve_wit_2_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (PreH1 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.undef_full ( &( "naf_k" ) ) 257 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (store_fn k_pre K_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_fn k_pre K_non_alias )
  **  (CharArray.undef_full (( &( "naf_k" ) ) + (0 * sizeof(CHAR))) 257 )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_3_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (PreH1 : (wnaf3_representation K_non_alias digits )) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UndefStructPredJPoint ( &( "Q" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_montg_one )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "z" .ₛ "v") 4 )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (PreH1 : (wnaf3_representation K_non_alias digits )) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (((( &( "naf_k" ) ) + (256 * sizeof(CHAR)))) # Char  |-> (Znth 256 digits 0))
  **  (CharArray.missing_i ( &( "naf_k" ) ) 256 0 257 digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_5_non_alias_pure := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (PreH1 : (wnaf3_representation K_non_alias digits )) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> (Znth 256 digits 0))
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((Znth (256) (digits) (0)) = (Znth (256) (digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ”
.

Definition montg_times_point_naf_w3_partial_solve_wit_5_non_alias_aux := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (PreH1 : (wnaf3_representation K_non_alias digits )) (PreH2 : (BasePoint_non_alias <> ECInfinity)) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  ((( &( "ki" ) )) # Char  |-> (Znth 256 digits 0))
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ ((Znth (256) (digits) (0)) = (Znth (256) (digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  ((( &( "ki" ) )) # Char  |-> (Znth (256) (digits) (0)))
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_5_non_alias := montg_times_point_naf_w3_partial_solve_wit_5_non_alias_pure -> montg_times_point_naf_w3_partial_solve_wit_5_non_alias_aux.

Definition montg_times_point_naf_w3_partial_solve_wit_6_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit > 0)) (PreH2 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH3 : (wnaf3_representation K_non_alias initial_digits )) (PreH4 : (wnaf3_digit first_digit )) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (first_digit * sizeof( "AFPoint" ))) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit > 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint (( &( "PT" ) ) + (first_digit * sizeof( "AFPoint" ))) (sm2_point_mul (first_digit) (BasePoint_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_7_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (digits: (@list Z)) (initial_digits: (@list Z)) (first_digit: Z) (PreH1 : (first_digit < 0)) (PreH2 : (first_digit <= 0)) (PreH3 : (first_digit = (Znth (256) (initial_digits) (0)))) (PreH4 : (wnaf3_representation K_non_alias initial_digits )) (PreH5 : (wnaf3_digit first_digit )) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (BasePoint_non_alias <> ECInfinity)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_montg_one )
  **  (store_mont_jpoint ( &( "Q" ) ) ECInfinity )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  “ (first_digit < 0) ” 
  &&  “ (first_digit <= 0) ” 
  &&  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (BasePoint_non_alias <> ECInfinity) ”
  &&  (store_mont_afpoint (( &( "NT" ) ) + ((-first_digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-first_digit)) (BasePoint_non_alias)))) )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &(( &( "Q" ) )->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias first_digit )
  **  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
  **  (store_fn k_pre K_non_alias )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
.

Definition montg_times_point_naf_w3_partial_solve_wit_8_non_alias_pure := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i >= 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |->_)
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ”
.

Definition montg_times_point_naf_w3_partial_solve_wit_8_non_alias_aux := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i >= 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_partial_solve_wit_8_non_alias := montg_times_point_naf_w3_partial_solve_wit_8_non_alias_pure -> montg_times_point_naf_w3_partial_solve_wit_8_non_alias_aux.

Definition montg_times_point_naf_w3_partial_solve_wit_9_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (( &( "Q" ) ) = ( &( "Q" ) ))) (PreH2 : (i >= 0)) (PreH3 : ((-1) <= i)) (PreH4 : (i <= 255)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (((( &( "naf_k" ) ) + (i * sizeof(CHAR)))) # Char  |-> (Znth i digits 0))
  **  (CharArray.missing_i ( &( "naf_k" ) ) i 0 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_partial_solve_wit_10_non_alias_pure := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i >= 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |-> (Znth i digits 0))
|--
  “ ((Znth (i) (digits) (0)) = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ”
.

Definition montg_times_point_naf_w3_partial_solve_wit_10_non_alias_aux := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (i >= 0)) (PreH2 : ((-1) <= i)) (PreH3 : (i <= 255)) (PreH4 : (0 <= K_non_alias)) (PreH5 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH6 : (wnaf3_representation K_non_alias digits )) (PreH7 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  ((( &( "ki" ) )) # Char  |-> (Znth i digits 0))
|--
  “ ((Znth (i) (digits) (0)) = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  ((( &( "ki" ) )) # Char  |-> (Znth (i) (digits) (0)))
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_partial_solve_wit_10_non_alias := montg_times_point_naf_w3_partial_solve_wit_10_non_alias_pure -> montg_times_point_naf_w3_partial_solve_wit_10_non_alias_aux.

Definition montg_times_point_naf_w3_partial_solve_wit_11_non_alias_pure := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (digit * sizeof( "AFPoint" ))) (sm2_point_mul (digit) (BasePoint_non_alias)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ”
.

Definition montg_times_point_naf_w3_partial_solve_wit_11_non_alias_aux := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit > 0)) (PreH2 : (digit = (Znth (i) (digits) (0)))) (PreH3 : (0 <= i)) (PreH4 : (i < 256)) (PreH5 : (wnaf3_representation K_non_alias digits )) (PreH6 : (wnaf3_digit digit )) (PreH7 : (i >= 0)) (PreH8 : ((-1) <= i)) (PreH9 : (i <= 255)) (PreH10 : (0 <= K_non_alias)) (PreH11 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH12 : (wnaf3_representation K_non_alias digits )) (PreH13 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH14 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "PT" ) ) + (digit * sizeof( "AFPoint" ))) (sm2_point_mul (digit) (BasePoint_non_alias)) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ” 
  &&  “ (digit > 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_mont_afpoint (( &( "PT" ) ) + (digit * sizeof( "AFPoint" ))) (sm2_point_mul (digit) (BasePoint_non_alias)) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
.

Definition montg_times_point_naf_w3_partial_solve_wit_11_non_alias := montg_times_point_naf_w3_partial_solve_wit_11_non_alias_pure -> montg_times_point_naf_w3_partial_solve_wit_11_non_alias_aux.

Definition montg_times_point_naf_w3_partial_solve_wit_12_non_alias_pure := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ki" ) )) # Char  |-> digit)
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  ((( &( "P" ) )) # Ptr  |-> P_pre)
  **  ((( &( "k" ) )) # Ptr  |-> k_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ”
.

Definition montg_times_point_naf_w3_partial_solve_wit_12_non_alias_aux := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (digit: Z) (PreH1 : (digit < 0)) (PreH2 : (i <= INT_MAX)) (PreH3 : (i >= INT_MIN)) (PreH4 : (digit <= 0)) (PreH5 : (digit = (Znth (i) (digits) (0)))) (PreH6 : (0 <= i)) (PreH7 : (i < 256)) (PreH8 : (wnaf3_representation K_non_alias digits )) (PreH9 : (wnaf3_digit digit )) (PreH10 : (i >= 0)) (PreH11 : ((-1) <= i)) (PreH12 : (i <= 255)) (PreH13 : (0 <= K_non_alias)) (PreH14 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH15 : (wnaf3_representation K_non_alias digits )) (PreH16 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) (PreH17 : (digit <> 0)) ,
  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (( &( "Q" ) ) = ( &( "Q" ) )) ” 
  &&  “ (digit < 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (digit <= 0) ” 
  &&  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ” 
  &&  “ (digit <> 0) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) (sm2_point_double (Acc)) )
  **  (store_mont_afpoint (( &( "NT" ) ) + ((-digit) * sizeof( "AFPoint" ))) (sm2_point_negate ((sm2_point_mul ((-digit)) (BasePoint_non_alias)))) )
  **  (store_bn_zero )
  **  (store_montg_one )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_mont_wnaf3_precomp_rest ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias digit )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
.

Definition montg_times_point_naf_w3_partial_solve_wit_12_non_alias := montg_times_point_naf_w3_partial_solve_wit_12_non_alias_pure -> montg_times_point_naf_w3_partial_solve_wit_12_non_alias_aux.

Definition montg_times_point_naf_w3_partial_solve_wit_13_non_alias := 
forall (result_pre: Z) (k_pre: Z) (P_pre: Z) (K_non_alias: Z) (BasePoint_non_alias: ec_point) (i: Z) (digits: (@list Z)) (Acc: ec_point) (PreH1 : (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias)))) (PreH2 : (i < 0)) (PreH3 : ((-1) <= i)) (PreH4 : (i <= 255)) (PreH5 : (0 <= K_non_alias)) (PreH6 : (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits)))))) (PreH7 : (wnaf3_representation K_non_alias digits )) (PreH8 : (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias)))) ,
  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
|--
  “ (Acc = (sm2_point_mul (K_non_alias) (BasePoint_non_alias))) ” 
  &&  “ (i < 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 255) ” 
  &&  “ (0 <= K_non_alias) ” 
  &&  “ (0 <= (wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (Acc = (sm2_point_mul ((wnaf3_value ((sublist ((i + 1 )) (257) (digits))))) (BasePoint_non_alias))) ”
  &&  (store_mont_jpoint ( &( "Q" ) ) Acc )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_afpoint P_pre BasePoint_non_alias )
  **  (store_fn k_pre K_non_alias )
  **  (store_mont_wnaf3_precomp ( &( "PT" ) ) ( &( "NT" ) ) BasePoint_non_alias )
  **  (wnaf3_precomp_unused ( &( "PT" ) ) ( &( "NT" ) ) )
  **  (CharArray.full ( &( "naf_k" ) ) 257 digits )
  **  (store_sm2_h )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_bn_zero )
  **  (store_montg_one )
.

Definition montg_times_point_naf_w3_which_implies_wit_1 := 
(
forall (K_non_alias: Z) (first_digit: Z) (initial_digits_2: (@list Z)) (PreH1 : (first_digit = (Znth (256) (initial_digits_2) (0)))) (PreH2 : (wnaf3_representation K_non_alias initial_digits_2 )) ,
  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits_2 )
|--
  EX (initial_digits: (@list Z)) ,
  “ (first_digit = (Znth (256) (initial_digits) (0))) ” 
  &&  “ (wnaf3_representation K_non_alias initial_digits ) ” 
  &&  “ (wnaf3_digit first_digit ) ”
  &&  (CharArray.full ( &( "naf_k" ) ) 257 initial_digits )
) \/
(
forall (K_non_alias: Z) (first_digit: Z) (initial_digits_2: (@list Z)) (PreH1 : (first_digit = (Znth (256) (initial_digits_2) (0)))) (PreH2 : (wnaf3_representation K_non_alias initial_digits_2 )) ,
  TT && emp 
|--
  “ (wnaf3_digit first_digit ) ”
  &&  emp
).

Definition montg_times_point_naf_w3_which_implies_wit_1_split_goal_1 := 
forall (K_non_alias: Z) (first_digit: Z) (initial_digits_2: (@list Z)) (PreH1 : (first_digit = (Znth (256) (initial_digits_2) (0)))) (PreH2 : (wnaf3_representation K_non_alias initial_digits_2 )) ,
  (wnaf3_digit first_digit )
.

Definition montg_times_point_naf_w3_which_implies_wit_2 := 
(
forall (K_non_alias: Z) (digits: (@list Z)) (digit: Z) (i: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) ,
  (CharArray.full ( &( "naf_k" ) ) 257 digits )
|--
  “ (digit = (Znth (i) (digits) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (wnaf3_representation K_non_alias digits ) ” 
  &&  “ (wnaf3_digit digit ) ”
  &&  (CharArray.full ( &( "naf_k" ) ) 257 digits )
) \/
(
forall (K_non_alias: Z) (digits: (@list Z)) (digit: Z) (i: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) ,
  TT && emp 
|--
  “ (wnaf3_digit digit ) ”
  &&  emp
).

Definition montg_times_point_naf_w3_which_implies_wit_2_split_goal_1 := 
forall (K_non_alias: Z) (digits: (@list Z)) (digit: Z) (i: Z) (PreH1 : (digit = (Znth (i) (digits) (0)))) (PreH2 : (0 <= i)) (PreH3 : (i < 256)) (PreH4 : (wnaf3_representation K_non_alias digits )) ,
  (wnaf3_digit digit )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.
Include ecc_point_overwrite_Strategy_Correct.
Include wnaf3_precomp_points_Strategy_Correct.
Include wnaf3_predicate_cancellation_Strategy_Correct.

Axiom proof_of_montg_times_point_naf_w3_safety_wit_1_non_alias : montg_times_point_naf_w3_safety_wit_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_2_non_alias : montg_times_point_naf_w3_safety_wit_2_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_3_non_alias : montg_times_point_naf_w3_safety_wit_3_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_4_non_alias : montg_times_point_naf_w3_safety_wit_4_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_5_non_alias : montg_times_point_naf_w3_safety_wit_5_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_6_non_alias : montg_times_point_naf_w3_safety_wit_6_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_7_non_alias : montg_times_point_naf_w3_safety_wit_7_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_8_non_alias : montg_times_point_naf_w3_safety_wit_8_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_9_non_alias : montg_times_point_naf_w3_safety_wit_9_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_10_non_alias : montg_times_point_naf_w3_safety_wit_10_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_11_non_alias : montg_times_point_naf_w3_safety_wit_11_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_12_non_alias : montg_times_point_naf_w3_safety_wit_12_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_13_non_alias : montg_times_point_naf_w3_safety_wit_13_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_14_non_alias : montg_times_point_naf_w3_safety_wit_14_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_15_non_alias : montg_times_point_naf_w3_safety_wit_15_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_16_non_alias : montg_times_point_naf_w3_safety_wit_16_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_17_non_alias : montg_times_point_naf_w3_safety_wit_17_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_18_non_alias : montg_times_point_naf_w3_safety_wit_18_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_19_non_alias : montg_times_point_naf_w3_safety_wit_19_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_20_non_alias : montg_times_point_naf_w3_safety_wit_20_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_21_non_alias : montg_times_point_naf_w3_safety_wit_21_non_alias.
Axiom proof_of_montg_times_point_naf_w3_safety_wit_22_non_alias : montg_times_point_naf_w3_safety_wit_22_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_1_non_alias : montg_times_point_naf_w3_entail_wit_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_2_non_alias : montg_times_point_naf_w3_entail_wit_2_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_3_non_alias : montg_times_point_naf_w3_entail_wit_3_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_4_non_alias : montg_times_point_naf_w3_entail_wit_4_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_5_non_alias : montg_times_point_naf_w3_entail_wit_5_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_6_non_alias : montg_times_point_naf_w3_entail_wit_6_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_7_non_alias : montg_times_point_naf_w3_entail_wit_7_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_8_non_alias : montg_times_point_naf_w3_entail_wit_8_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_9_non_alias : montg_times_point_naf_w3_entail_wit_9_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_10_non_alias : montg_times_point_naf_w3_entail_wit_10_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_11_non_alias : montg_times_point_naf_w3_entail_wit_11_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_12_non_alias : montg_times_point_naf_w3_entail_wit_12_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_13_non_alias : montg_times_point_naf_w3_entail_wit_13_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_14_non_alias : montg_times_point_naf_w3_entail_wit_14_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_15_1_non_alias : montg_times_point_naf_w3_entail_wit_15_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_15_2_non_alias : montg_times_point_naf_w3_entail_wit_15_2_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_15_3_non_alias : montg_times_point_naf_w3_entail_wit_15_3_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_16_1_non_alias : montg_times_point_naf_w3_entail_wit_16_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_16_2_non_alias : montg_times_point_naf_w3_entail_wit_16_2_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_16_3_non_alias : montg_times_point_naf_w3_entail_wit_16_3_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_17_non_alias : montg_times_point_naf_w3_entail_wit_17_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_18_non_alias : montg_times_point_naf_w3_entail_wit_18_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_19_non_alias : montg_times_point_naf_w3_entail_wit_19_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_20_non_alias : montg_times_point_naf_w3_entail_wit_20_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_21_non_alias : montg_times_point_naf_w3_entail_wit_21_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_22_non_alias : montg_times_point_naf_w3_entail_wit_22_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_23_non_alias : montg_times_point_naf_w3_entail_wit_23_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_24_non_alias : montg_times_point_naf_w3_entail_wit_24_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_25_1_non_alias : montg_times_point_naf_w3_entail_wit_25_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_25_2_non_alias : montg_times_point_naf_w3_entail_wit_25_2_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_25_3_non_alias : montg_times_point_naf_w3_entail_wit_25_3_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_26_non_alias : montg_times_point_naf_w3_entail_wit_26_non_alias.
Axiom proof_of_montg_times_point_naf_w3_entail_wit_27_non_alias : montg_times_point_naf_w3_entail_wit_27_non_alias.
Axiom proof_of_montg_times_point_naf_w3_return_wit_1_non_alias : montg_times_point_naf_w3_return_wit_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_1_non_alias_pure : montg_times_point_naf_w3_partial_solve_wit_1_non_alias_pure.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_1_non_alias : montg_times_point_naf_w3_partial_solve_wit_1_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_2_non_alias : montg_times_point_naf_w3_partial_solve_wit_2_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_3_non_alias : montg_times_point_naf_w3_partial_solve_wit_3_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_4_non_alias : montg_times_point_naf_w3_partial_solve_wit_4_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_5_non_alias_pure : montg_times_point_naf_w3_partial_solve_wit_5_non_alias_pure.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_5_non_alias : montg_times_point_naf_w3_partial_solve_wit_5_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_6_non_alias : montg_times_point_naf_w3_partial_solve_wit_6_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_7_non_alias : montg_times_point_naf_w3_partial_solve_wit_7_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_8_non_alias_pure : montg_times_point_naf_w3_partial_solve_wit_8_non_alias_pure.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_8_non_alias : montg_times_point_naf_w3_partial_solve_wit_8_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_9_non_alias : montg_times_point_naf_w3_partial_solve_wit_9_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_10_non_alias_pure : montg_times_point_naf_w3_partial_solve_wit_10_non_alias_pure.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_10_non_alias : montg_times_point_naf_w3_partial_solve_wit_10_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_11_non_alias_pure : montg_times_point_naf_w3_partial_solve_wit_11_non_alias_pure.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_11_non_alias : montg_times_point_naf_w3_partial_solve_wit_11_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_12_non_alias_pure : montg_times_point_naf_w3_partial_solve_wit_12_non_alias_pure.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_12_non_alias : montg_times_point_naf_w3_partial_solve_wit_12_non_alias.
Axiom proof_of_montg_times_point_naf_w3_partial_solve_wit_13_non_alias : montg_times_point_naf_w3_partial_solve_wit_13_non_alias.
Axiom proof_of_montg_times_point_naf_w3_which_implies_wit_1 : montg_times_point_naf_w3_which_implies_wit_1.
Axiom proof_of_montg_times_point_naf_w3_which_implies_wit_2 : montg_times_point_naf_w3_which_implies_wit_2.

End VC_Correct.
