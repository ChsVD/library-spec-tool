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
Require Import SimpleC.EE.Applications_human.sm2.lib.ec_math_refinement.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import array_bridges_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import jpoint_double_trace_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import jpoint_double_trace_strategy_proof.

(*----- Function double_JPoint -----*)

Definition double_JPoint_safety_wit_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P_in_place = ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition double_JPoint_safety_wit_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P_non_alias = ECInfinity)) (PreH5 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition double_JPoint_safety_wit_3_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P_in_place <> ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition double_JPoint_safety_wit_4_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition double_JPoint_entail_wit_1_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (PreH1 : (result_pre = pt_pre)) ,
  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (result_pre = pt_pre) ”
  &&  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  ((UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_1_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) ,
  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (result_pre = pt_pre) ”
  &&  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  ((UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_2_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (P_in_place = ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval_3 = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_2_2_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P_in_place <> ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_2_3_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (P_non_alias = ECInfinity)) (PreH5 : (retval_3 = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_2_4_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_2 = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_3_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P_in_place = ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_3_2_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_in_place <> ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval_3 <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_3_3_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P_non_alias = ECInfinity)) (PreH5 : (retval_2 <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_3_4_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval_3 <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_4_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P_in_place = ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (z: Z)  (y: Z)  (x: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P_in_place ) ” 
  &&  “ (jpoint_represents x y z P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields pt_pre x y z )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z)  (retval_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields pt_pre x_2 y_2 z_2 )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_4_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P_non_alias = ECInfinity)) (PreH5 : (retval_2 <> 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (z: Z)  (y: Z)  (x: Z)  (retval: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P_in_place ) ” 
  &&  “ (jpoint_represents x y z P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields pt_pre x y z )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields pt_pre x_2 y_2 z_2 )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_5_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P_in_place )) (PreH2 : (jpoint_represents x y z P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P_in_place = ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval <> 0)) ,
  (store_jpoint_fields pt_pre x y z )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (zs: (@list Z))  (ys: (@list Z))  (xs: (@list Z)) ,
  “ ((u64_list_value (zs)) = z) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ ((u64_list_value (ys)) = y) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((u64_list_value (xs)) = x) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P_in_place ) ” 
  &&  “ (jpoint_represents x y z P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (zs_2: (@list Z))  (ys_2: (@list Z))  (xs_2: (@list Z))  (z_2: Z)  (y_2: Z)  (x_2: Z)  (retval_2: Z) ,
  “ ((u64_list_value (zs_2)) = z_2) ” 
  &&  “ (u64_list_bounded zs_2 ) ” 
  &&  “ ((Zlength (zs_2)) = 4) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ ((u64_list_value (ys_2)) = y_2) ” 
  &&  “ (u64_list_bounded ys_2 ) ” 
  &&  “ ((Zlength (ys_2)) = 4) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ ((u64_list_value (xs_2)) = x_2) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs_2 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys_2 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs_2 )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_5_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (x_2: Z) (y_2: Z) (z_2: Z) (PreH1 : (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P_non_alias )) (PreH2 : (jpoint_represents x_2 y_2 z_2 P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 1)) (PreH6 : (P_non_alias = ECInfinity)) (PreH7 : (retval_2 <> 0)) ,
  (store_jpoint_fields pt_pre x_2 y_2 z_2 )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (zs: (@list Z))  (ys: (@list Z))  (xs: (@list Z))  (z: Z)  (y: Z)  (x: Z)  (retval: Z) ,
  “ ((u64_list_value (zs)) = z) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ ((u64_list_value (ys)) = y) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((u64_list_value (xs)) = x) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P_in_place ) ” 
  &&  “ (jpoint_represents x y z P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_in_place = ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval <> 0) ”
  &&  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (zs_2: (@list Z))  (ys_2: (@list Z))  (xs_2: (@list Z)) ,
  “ ((u64_list_value (zs_2)) = z_2) ” 
  &&  “ (u64_list_bounded zs_2 ) ” 
  &&  “ ((Zlength (zs_2)) = 4) ” 
  &&  “ (z_2 < SM2_P_Z) ” 
  &&  “ (0 <= z_2) ” 
  &&  “ ((u64_list_value (ys_2)) = y_2) ” 
  &&  “ (u64_list_bounded ys_2 ) ” 
  &&  “ ((Zlength (ys_2)) = 4) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ ((u64_list_value (xs_2)) = x_2) ” 
  &&  “ (u64_list_bounded xs_2 ) ” 
  &&  “ ((Zlength (xs_2)) = 4) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs_2 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys_2 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs_2 )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_6_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp ( &( "S" ) ) (Zmod ((2 * JY_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  (“ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_6_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp ( &( "S" ) ) (Zmod ((2 * JY_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop ))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_rhop ))
.

Definition double_JPoint_entail_wit_7_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp ( &( "U" ) ) (Zmod ((JZ_in_place * JZ_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_7_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp ( &( "U" ) ) (Zmod ((JZ_non_alias * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_8_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (Zmod (((jdouble_trace_s2 (JY_in_place)) * (jdouble_trace_s2 (JY_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_8_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (Zmod (((jdouble_trace_s2 (JY_non_alias)) * (jdouble_trace_s2 (JY_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  (UndefStructPredJPoint result_pre )
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_9_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((jdouble_trace_m4 (JY_in_place)) * (jdouble_trace_m4 (JY_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_9_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((jdouble_trace_m4 (JY_non_alias)) * (jdouble_trace_m4 (JY_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_10_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp ( &( "S" ) ) (Zmod (((jdouble_trace_m4 (JY_in_place)) * JX_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_10_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "S" ) ) (Zmod (((jdouble_trace_m4 (JY_non_alias)) * JX_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_11_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (fp_div2 ((jdouble_trace_t16 (JY_in_place)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_11_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (fp_div2 ((jdouble_trace_t16 (JY_non_alias)))) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_12_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp ( &( "M" ) ) (Zmod (((jdouble_trace_z2 (JZ_in_place)) + JX_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_12_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "M" ) ) (Zmod (((jdouble_trace_z2 (JZ_non_alias)) + JX_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_13_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U" ) ) = ( &( "U" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp ( &( "U" ) ) (Zmod ((JX_in_place - (jdouble_trace_z2 (JZ_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (( &( "U" ) ) = ( &( "U" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (( &( "U" ) ) = ( &( "U" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_13_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U" ) ) = ( &( "U" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "U" ) ) (Zmod ((JX_non_alias - (jdouble_trace_z2 (JZ_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (( &( "U" ) ) = ( &( "U" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (( &( "U" ) ) = ( &( "U" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_14_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (Zmod (((jdouble_trace_sum (JX_in_place) (JZ_in_place)) * (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_14_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp ( &( "M" ) ) (Zmod (((jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) * (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_15_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (Zmod ((3 * (jdouble_trace_prod (JX_in_place) (JZ_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_15_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp ( &( "M" ) ) (Zmod ((3 * (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_16_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "U" ) ) (Zmod ((2 * (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_16_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "U" ) ) (Zmod ((2 * (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_17_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((jdouble_trace_slope (JX_in_place) (JZ_in_place)) * (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_17_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval_2 = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) * (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_18_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) - (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_18_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) - (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_19_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (Zmod (((jdouble_trace_s4 (JX_in_place) (JY_in_place)) - (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_19_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp ( &( "S" ) ) (Zmod (((jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) - (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_20_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (Zmod (((jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) * (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_20_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp ( &( "S" ) ) (Zmod (((jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) * (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_21_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) - (jdouble_trace_t8 (JY_in_place)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (“ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (EX (retval_2: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_entail_wit_21_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (P_in_place: ec_point) (retval_2: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval_2 = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) - (jdouble_trace_t8 (JY_non_alias)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  (EX (retval: Z) ,
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
  ||
  (“ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre))
.

Definition double_JPoint_return_wit_1_non_alias := 
(
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = z)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (z < SM2_P_Z)) (PreH5 : (0 <= z)) (PreH6 : ((u64_list_value (ys)) = y)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (y < SM2_P_Z)) (PreH10 : (0 <= y)) (PreH11 : ((u64_list_value (xs)) = x)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (x < SM2_P_Z)) (PreH15 : (0 <= x)) (PreH16 : (jpoint_canonical_infinity_encoding x y z P_non_alias )) (PreH17 : (jpoint_represents x y z P_non_alias )) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (retval = 1)) (PreH21 : (P_non_alias = ECInfinity)) (PreH22 : (retval <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (P_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = z)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (z < SM2_P_Z)) (PreH5 : (0 <= z)) (PreH6 : ((u64_list_value (ys)) = y)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (y < SM2_P_Z)) (PreH10 : (0 <= y)) (PreH11 : ((u64_list_value (xs)) = x)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (x < SM2_P_Z)) (PreH15 : (0 <= x)) (PreH16 : (jpoint_canonical_infinity_encoding x y z P_non_alias )) (PreH17 : (jpoint_represents x y z P_non_alias )) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (retval = 1)) (PreH21 : (P_non_alias = ECInfinity)) (PreH22 : (retval <> 0)) ,
  TT && emp 
|--
  “ (jpoint_represents x y z (sm2_point_double (ECInfinity)) ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z (sm2_point_double (ECInfinity)) ) ”
  &&  emp
).

Definition double_JPoint_return_wit_1_non_alias_split_goal_1 := 
forall (P_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = z)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (z < SM2_P_Z)) (PreH5 : (0 <= z)) (PreH6 : ((u64_list_value (ys)) = y)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (y < SM2_P_Z)) (PreH10 : (0 <= y)) (PreH11 : ((u64_list_value (xs)) = x)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (x < SM2_P_Z)) (PreH15 : (0 <= x)) (PreH16 : (jpoint_canonical_infinity_encoding x y z P_non_alias )) (PreH17 : (jpoint_represents x y z P_non_alias )) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (retval = 1)) (PreH21 : (P_non_alias = ECInfinity)) (PreH22 : (retval <> 0)) ,
  (jpoint_represents x y z (sm2_point_double (ECInfinity)) )
.

Definition double_JPoint_return_wit_1_non_alias_split_goal_2 := 
forall (P_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = z)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (z < SM2_P_Z)) (PreH5 : (0 <= z)) (PreH6 : ((u64_list_value (ys)) = y)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (y < SM2_P_Z)) (PreH10 : (0 <= y)) (PreH11 : ((u64_list_value (xs)) = x)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (x < SM2_P_Z)) (PreH15 : (0 <= x)) (PreH16 : (jpoint_canonical_infinity_encoding x y z P_non_alias )) (PreH17 : (jpoint_represents x y z P_non_alias )) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (retval = 1)) (PreH21 : (P_non_alias = ECInfinity)) (PreH22 : (retval <> 0)) ,
  (jpoint_canonical_infinity_encoding x y z (sm2_point_double (ECInfinity)) )
.

Definition double_JPoint_return_wit_2_in_place := 
(
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = z)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (z < SM2_P_Z)) (PreH5 : (0 <= z)) (PreH6 : ((u64_list_value (ys)) = y)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (y < SM2_P_Z)) (PreH10 : (0 <= y)) (PreH11 : ((u64_list_value (xs)) = x)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (x < SM2_P_Z)) (PreH15 : (0 <= x)) (PreH16 : (jpoint_canonical_infinity_encoding x y z P_in_place )) (PreH17 : (jpoint_represents x y z P_in_place )) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (retval = 1)) (PreH21 : (P_in_place = ECInfinity)) (PreH22 : (result_pre = pt_pre)) (PreH23 : (retval <> 0)) ,
  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = pt_pre) ”
  &&  (store_jpoint_with_canonical_infinity result_pre (sm2_point_double (P_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((Znth (3) (xs) (0)) < U64_MOD)) (PreH2 : (0 <= (Znth (3) (xs) (0)))) (PreH3 : ((Znth (3) (ys) (0)) < U64_MOD)) (PreH4 : (0 <= (Znth (3) (ys) (0)))) (PreH5 : ((Znth (3) (zs) (0)) < U64_MOD)) (PreH6 : (0 <= (Znth (3) (zs) (0)))) (PreH7 : ((u64_list_value (zs)) = z)) (PreH8 : (u64_list_bounded zs )) (PreH9 : ((Zlength (zs)) = 4)) (PreH10 : (z < SM2_P_Z)) (PreH11 : (0 <= z)) (PreH12 : ((u64_list_value (ys)) = y)) (PreH13 : (u64_list_bounded ys )) (PreH14 : ((Zlength (ys)) = 4)) (PreH15 : (y < SM2_P_Z)) (PreH16 : (0 <= y)) (PreH17 : ((u64_list_value (xs)) = x)) (PreH18 : (u64_list_bounded xs )) (PreH19 : ((Zlength (xs)) = 4)) (PreH20 : (x < SM2_P_Z)) (PreH21 : (0 <= x)) (PreH22 : (jpoint_canonical_infinity_encoding x y z P_in_place )) (PreH23 : (jpoint_represents x y z P_in_place )) (PreH24 : (0 <= retval)) (PreH25 : (retval <= 1)) (PreH26 : (retval = 1)) (PreH27 : (P_in_place = ECInfinity)) (PreH28 : (result_pre = pt_pre)) (PreH29 : (retval <> 0)) ,
  (UInt64Array.missing_i &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 3 0 4 xs )
  **  (UInt64Array.missing_i &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 3 0 4 ys )
  **  (UInt64Array.missing_i &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 3 0 4 zs )
|--
  EX (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ ((Znth (3) (xs) (0)) < U64_MOD) ” 
  &&  “ (0 <= (Znth (3) (xs) (0))) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) ((Znth (3) (xs) (0)))) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_3) (x1_3) (x2_3) ((Znth (3) (xs) (0))))) ” 
  &&  “ ((Znth (3) (ys) (0)) < U64_MOD) ” 
  &&  “ (0 <= (Znth (3) (ys) (0))) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) ((Znth (3) (ys) (0)))) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_2) (x1_2) (x2_2) ((Znth (3) (ys) (0))))) ” 
  &&  “ ((Znth (3) (zs) (0)) < U64_MOD) ” 
  &&  “ (0 <= (Znth (3) (zs) (0))) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) ((Znth (3) (zs) (0)))) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0) (x1) (x2) ((Znth (3) (zs) (0))))) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_3) (x1_3) (x2_3) ((Znth (3) (xs) (0)))) (u256_of_limbs (x0_2) (x1_2) (x2_2) ((Znth (3) (ys) (0)))) (u256_of_limbs (x0) (x1) (x2) ((Znth (3) (zs) (0)))) (sm2_point_double (P_in_place)) ) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_3) (x1_3) (x2_3) ((Znth (3) (xs) (0)))) (u256_of_limbs (x0_2) (x1_2) (x2_2) ((Znth (3) (ys) (0)))) (u256_of_limbs (x0) (x1) (x2) ((Znth (3) (zs) (0)))) (sm2_point_double (P_in_place)) ) ” 
  &&  “ (result_pre = pt_pre) ”
  &&  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition double_JPoint_return_wit_3_in_place := 
(
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (result_pre = pt_pre) ”
  &&  (store_jpoint_with_canonical_infinity result_pre (sm2_point_double (P_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  TT && emp 
|--
  “ (jpoint_represents (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) (sm2_point_double (P_in_place)) ) ” 
  &&  “ (jpoint_canonical_infinity_encoding (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) (sm2_point_double (P_in_place)) ) ”
  &&  emp
).

Definition double_JPoint_return_wit_3_in_place_split_goal_1 := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (jpoint_represents (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) (sm2_point_double (P_in_place)) )
.

Definition double_JPoint_return_wit_3_in_place_split_goal_2 := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (jpoint_canonical_infinity_encoding (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) (jdouble_trace_ry (JX_in_place) (JY_in_place) (JZ_in_place)) (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) (sm2_point_double (P_in_place)) )
.

Definition double_JPoint_return_wit_4_non_alias := 
(
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre (sm2_point_double (P_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  TT && emp 
|--
  “ (jpoint_represents (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) (sm2_point_double (P_non_alias)) ) ” 
  &&  “ (jpoint_canonical_infinity_encoding (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) (sm2_point_double (P_non_alias)) ) ”
  &&  emp
).

Definition double_JPoint_return_wit_4_non_alias_split_goal_1 := 
forall (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (jpoint_represents (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) (sm2_point_double (P_non_alias)) )
.

Definition double_JPoint_return_wit_4_non_alias_split_goal_2 := 
forall (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (jpoint_canonical_infinity_encoding (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (jdouble_trace_ry (JX_non_alias) (JY_non_alias) (JZ_non_alias)) (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) (sm2_point_double (P_non_alias)) )
.

Definition double_JPoint_partial_solve_wit_1_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (PreH1 : (result_pre = pt_pre)) ,
  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = pt_pre) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_2_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) ,
  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_3_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (xs: (@list Z)) (ys: (@list Z)) (zs: (@list Z)) (PreH1 : ((u64_list_value (zs)) = z)) (PreH2 : (u64_list_bounded zs )) (PreH3 : ((Zlength (zs)) = 4)) (PreH4 : (z < SM2_P_Z)) (PreH5 : (0 <= z)) (PreH6 : ((u64_list_value (ys)) = y)) (PreH7 : (u64_list_bounded ys )) (PreH8 : ((Zlength (ys)) = 4)) (PreH9 : (y < SM2_P_Z)) (PreH10 : (0 <= y)) (PreH11 : ((u64_list_value (xs)) = x)) (PreH12 : (u64_list_bounded xs )) (PreH13 : ((Zlength (xs)) = 4)) (PreH14 : (x < SM2_P_Z)) (PreH15 : (0 <= x)) (PreH16 : (jpoint_canonical_infinity_encoding x y z P_non_alias )) (PreH17 : (jpoint_represents x y z P_non_alias )) (PreH18 : (0 <= retval)) (PreH19 : (retval <= 1)) (PreH20 : (retval = 1)) (PreH21 : (P_non_alias = ECInfinity)) (PreH22 : (retval <> 0)) ,
  (UndefStructPredJPoint result_pre )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ ((u64_list_value (zs)) = z) ” 
  &&  “ (u64_list_bounded zs ) ” 
  &&  “ ((Zlength (zs)) = 4) ” 
  &&  “ (z < SM2_P_Z) ” 
  &&  “ (0 <= z) ” 
  &&  “ ((u64_list_value (ys)) = y) ” 
  &&  “ (u64_list_bounded ys ) ” 
  &&  “ ((Zlength (ys)) = 4) ” 
  &&  “ (y < SM2_P_Z) ” 
  &&  “ (0 <= y) ” 
  &&  “ ((u64_list_value (xs)) = x) ” 
  &&  “ (u64_list_bounded xs ) ” 
  &&  “ ((Zlength (xs)) = 4) ” 
  &&  “ (x < SM2_P_Z) ” 
  &&  “ (0 <= x) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P_non_alias ) ” 
  &&  “ (jpoint_represents x y z P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_non_alias = ECInfinity) ” 
  &&  “ (retval <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 zs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 ys )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &((pt_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 xs )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_4_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P_non_alias <> ECInfinity)) (PreH5 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_5_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P_in_place <> ECInfinity)) (PreH5 : (result_pre = pt_pre)) (PreH6 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity pt_pre P_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_6_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_jpoint_fields pt_pre JX_in_place JY_in_place JZ_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (UInt64Array.undef_full &(( &( "S" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_7_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_jpoint_fields pt_pre JX_non_alias JY_non_alias JZ_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredu32 ( &( "S" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (UInt64Array.undef_full &(( &( "S" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_rhop )
.

Definition double_JPoint_partial_solve_wit_8_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (store_sm2_rhop )
|--
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (UInt64Array.undef_full &(( &( "U" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
.

Definition double_JPoint_partial_solve_wit_9_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredu32 ( &( "U" ) ) )
  **  (UndefStructPredJPoint result_pre )
  **  (store_sm2_rhop )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (UInt64Array.undef_full &(( &( "U" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredJPoint result_pre )
.

Definition double_JPoint_partial_solve_wit_10_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (UndefStructPredu32 ( &( "M" ) ) )
|--
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (UInt64Array.undef_full &(( &( "M" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
.

Definition double_JPoint_partial_solve_wit_11_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredu32 ( &( "M" ) ) )
  **  (UndefStructPredJPoint result_pre )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "M" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredJPoint result_pre )
.

Definition double_JPoint_partial_solve_wit_12_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ”
.

Definition double_JPoint_partial_solve_wit_12_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH2 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_in_place <> ECInfinity)) (PreH7 : (result_pre = pt_pre)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
.

Definition double_JPoint_partial_solve_wit_12_in_place := double_JPoint_partial_solve_wit_12_in_place_pure -> double_JPoint_partial_solve_wit_12_in_place_aux.

Definition double_JPoint_partial_solve_wit_13_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UndefStructPredJPoint result_pre )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
.

Definition double_JPoint_partial_solve_wit_14_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_in_place )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
.

Definition double_JPoint_partial_solve_wit_15_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
.

Definition double_JPoint_partial_solve_wit_16_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (UInt64Array.undef_full &(( &( "S" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
.

Definition double_JPoint_partial_solve_wit_17_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s2 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UInt64Array.undef_full &(( &( "S" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_18_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition double_JPoint_partial_solve_wit_18_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
.

Definition double_JPoint_partial_solve_wit_18_in_place := double_JPoint_partial_solve_wit_18_in_place_pure -> double_JPoint_partial_solve_wit_18_in_place_aux.

Definition double_JPoint_partial_solve_wit_19_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition double_JPoint_partial_solve_wit_19_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t16 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_19_non_alias := double_JPoint_partial_solve_wit_19_non_alias_pure -> double_JPoint_partial_solve_wit_19_non_alias_aux.

Definition double_JPoint_partial_solve_wit_20_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (UInt64Array.undef_full &(( &( "M" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_21_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y"))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_m4 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (UInt64Array.undef_full &(( &( "M" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_22_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "U" ) ) = ( &( "U" ) )) ”
.

Definition double_JPoint_partial_solve_wit_22_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (( &( "U" ) ) = ( &( "U" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_22_in_place := double_JPoint_partial_solve_wit_22_in_place_pure -> double_JPoint_partial_solve_wit_22_in_place_aux.

Definition double_JPoint_partial_solve_wit_23_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "U" ) ) = ( &( "U" ) )) ”
.

Definition double_JPoint_partial_solve_wit_23_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (( &( "U" ) ) = ( &( "U" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_z2 (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_23_non_alias := double_JPoint_partial_solve_wit_23_non_alias_pure -> double_JPoint_partial_solve_wit_23_non_alias_aux.

Definition double_JPoint_partial_solve_wit_24_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U" ) ) = ( &( "U" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ”
.

Definition double_JPoint_partial_solve_wit_24_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "U" ) ) = ( &( "U" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_24_in_place := double_JPoint_partial_solve_wit_24_in_place_pure -> double_JPoint_partial_solve_wit_24_in_place_aux.

Definition double_JPoint_partial_solve_wit_25_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "U" ) ) = ( &( "U" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ”
.

Definition double_JPoint_partial_solve_wit_25_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "U" ) ) = ( &( "U" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_sum (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_25_non_alias := double_JPoint_partial_solve_wit_25_non_alias_pure -> double_JPoint_partial_solve_wit_25_non_alias_aux.

Definition double_JPoint_partial_solve_wit_26_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ”
.

Definition double_JPoint_partial_solve_wit_26_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_26_in_place := double_JPoint_partial_solve_wit_26_in_place_pure -> double_JPoint_partial_solve_wit_26_in_place_aux.

Definition double_JPoint_partial_solve_wit_27_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ”
.

Definition double_JPoint_partial_solve_wit_27_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (( &( "M" ) ) = ( &( "M" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_prod (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_27_non_alias := double_JPoint_partial_solve_wit_27_non_alias_pure -> double_JPoint_partial_solve_wit_27_non_alias_aux.

Definition double_JPoint_partial_solve_wit_28_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (UInt64Array.undef_full &(( &( "U" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_29_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "M" ) ) = ( &( "M" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_diff (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (UInt64Array.undef_full &(( &( "U" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_30_in_place := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_in_place )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_31_non_alias := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_32_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition double_JPoint_partial_solve_wit_32_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH3 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_in_place <> ECInfinity)) (PreH8 : (result_pre = pt_pre)) (PreH9 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_32_in_place := double_JPoint_partial_solve_wit_32_in_place_pure -> double_JPoint_partial_solve_wit_32_in_place_aux.

Definition double_JPoint_partial_solve_wit_33_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition double_JPoint_partial_solve_wit_33_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 0)) (PreH6 : (P_non_alias <> ECInfinity)) (PreH7 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_slope_sq (JX_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_33_non_alias := double_JPoint_partial_solve_wit_33_non_alias_pure -> double_JPoint_partial_solve_wit_33_non_alias_aux.

Definition double_JPoint_partial_solve_wit_34_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ”
.

Definition double_JPoint_partial_solve_wit_34_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_34_in_place := double_JPoint_partial_solve_wit_34_in_place_pure -> double_JPoint_partial_solve_wit_34_in_place_aux.

Definition double_JPoint_partial_solve_wit_35_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ”
.

Definition double_JPoint_partial_solve_wit_35_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_s4 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_35_non_alias := double_JPoint_partial_solve_wit_35_non_alias_pure -> double_JPoint_partial_solve_wit_35_non_alias_aux.

Definition double_JPoint_partial_solve_wit_36_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ”
.

Definition double_JPoint_partial_solve_wit_36_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_36_in_place := double_JPoint_partial_solve_wit_36_in_place_pure -> double_JPoint_partial_solve_wit_36_in_place_aux.

Definition double_JPoint_partial_solve_wit_37_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ”
.

Definition double_JPoint_partial_solve_wit_37_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (( &( "S" ) ) = ( &( "S" ) )) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_37_non_alias := double_JPoint_partial_solve_wit_37_non_alias_pure -> double_JPoint_partial_solve_wit_37_non_alias_aux.

Definition double_JPoint_partial_solve_wit_38_in_place_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition double_JPoint_partial_solve_wit_38_in_place_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_in_place: ec_point) (retval: Z) (JX_in_place: Z) (JY_in_place: Z) (JZ_in_place: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z"))) (PreH3 : (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH4 : (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place )) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P_in_place <> ECInfinity)) (PreH9 : (result_pre = pt_pre)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((pt_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_in_place <> ECInfinity) ” 
  &&  “ (result_pre = pt_pre) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_in_place)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_in_place) (JZ_in_place)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_in_place) (JY_in_place) (JZ_in_place)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_in_place) (JY_in_place)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_in_place)) * JZ_in_place )) (SM2_P_Z)) )
.

Definition double_JPoint_partial_solve_wit_38_in_place := double_JPoint_partial_solve_wit_38_in_place_pure -> double_JPoint_partial_solve_wit_38_in_place_aux.

Definition double_JPoint_partial_solve_wit_39_non_alias_pure := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
  **  ((( &( "pt" ) )) # Ptr  |-> pt_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ”
.

Definition double_JPoint_partial_solve_wit_39_non_alias_aux := 
forall (result_pre: Z) (pt_pre: Z) (P_non_alias: ec_point) (retval: Z) (JX_non_alias: Z) (JY_non_alias: Z) (JZ_non_alias: Z) (PreH1 : (( &( "S" ) ) = ( &( "S" ) ))) (PreH2 : (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH3 : (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias )) (PreH4 : (0 <= retval)) (PreH5 : (retval <= 1)) (PreH6 : (retval = 0)) (PreH7 : (P_non_alias <> ECInfinity)) (PreH8 : (retval = 0)) ,
  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "y") = &((result_pre)  # "JPoint" ->ₛ "y")) ” 
  &&  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_non_alias <> ECInfinity) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "S" ) ) (jdouble_trace_tmp2 (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (jdouble_trace_t8 (JY_non_alias)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "M" ) ) (jdouble_trace_slope (JX_non_alias) (JZ_non_alias)) )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (jdouble_trace_rx (JX_non_alias) (JY_non_alias) (JZ_non_alias)) )
  **  (store_fp ( &( "U" ) ) (jdouble_trace_u8 (JX_non_alias) (JY_non_alias)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "x") JX_non_alias )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "z") JZ_non_alias )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod (((jdouble_trace_s2 (JY_non_alias)) * JZ_non_alias )) (SM2_P_Z)) )
  **  (store_fp &((pt_pre)  # "JPoint" ->ₛ "y") JY_non_alias )
.

Definition double_JPoint_partial_solve_wit_39_non_alias := double_JPoint_partial_solve_wit_39_non_alias_pure -> double_JPoint_partial_solve_wit_39_non_alias_aux.

Definition double_JPoint_which_implies_wit_1 := 
(
forall (P_non_alias: ec_point) (pt: Z) ,
  (store_jpoint_with_canonical_infinity pt P_non_alias )
|--
  EX (JX_non_alias: Z)  (JY_non_alias: Z)  (JZ_non_alias: Z) ,
  “ (jpoint_represents JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_non_alias JY_non_alias JZ_non_alias P_non_alias ) ”
  &&  (store_jpoint_fields pt JX_non_alias JY_non_alias JZ_non_alias )
) \/
(
forall (P_non_alias: ec_point) (pt: Z) ,
  (store_jpoint_with_canonical_infinity pt P_non_alias )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) P_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) P_non_alias ) ”
  &&  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Definition double_JPoint_which_implies_wit_2 := 
(
forall (P_in_place: ec_point) (pt: Z) ,
  (store_jpoint_with_canonical_infinity pt P_in_place )
|--
  EX (JX_in_place: Z)  (JY_in_place: Z)  (JZ_in_place: Z) ,
  “ (jpoint_represents JX_in_place JY_in_place JZ_in_place P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX_in_place JY_in_place JZ_in_place P_in_place ) ”
  &&  (store_jpoint_fields pt JX_in_place JY_in_place JZ_in_place )
) \/
(
forall (P_in_place: ec_point) (pt: Z) ,
  (store_jpoint_with_canonical_infinity pt P_in_place )
|--
  EX (x3_3: Z)  (x2_3: Z)  (x1_3: Z)  (x0_3: Z)  (x3_2: Z)  (x2_2: Z)  (x1_2: Z)  (x0_2: Z)  (x3: Z)  (x2: Z)  (x1: Z)  (x0: Z) ,
  “ (x3_3 < U64_MOD) ” 
  &&  “ (0 <= x3_3) ” 
  &&  “ (x2_3 < U64_MOD) ” 
  &&  “ (0 <= x2_3) ” 
  &&  “ (x1_3 < U64_MOD) ” 
  &&  “ (0 <= x1_3) ” 
  &&  “ (x0_3 < U64_MOD) ” 
  &&  “ (0 <= x0_3) ” 
  &&  “ ((u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3))) ” 
  &&  “ (x3_2 < U64_MOD) ” 
  &&  “ (0 <= x3_2) ” 
  &&  “ (x2_2 < U64_MOD) ” 
  &&  “ (0 <= x2_2) ” 
  &&  “ (x1_2 < U64_MOD) ” 
  &&  “ (0 <= x1_2) ” 
  &&  “ (x0_2 < U64_MOD) ” 
  &&  “ (0 <= x0_2) ” 
  &&  “ ((u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2))) ” 
  &&  “ (x3 < U64_MOD) ” 
  &&  “ (0 <= x3) ” 
  &&  “ (x2 < U64_MOD) ” 
  &&  “ (0 <= x2) ” 
  &&  “ (x1 < U64_MOD) ” 
  &&  “ (0 <= x1) ” 
  &&  “ (x0 < U64_MOD) ” 
  &&  “ (0 <= x0) ” 
  &&  “ ((u256_of_limbs (x0) (x1) (x2) (x3)) < SM2_P_Z) ” 
  &&  “ (0 <= (u256_of_limbs (x0) (x1) (x2) (x3))) ” 
  &&  “ (jpoint_represents (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) P_in_place ) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u256_of_limbs (x0_3) (x1_3) (x2_3) (x3_3)) (u256_of_limbs (x0_2) (x1_2) (x2_2) (x3_2)) (u256_of_limbs (x0) (x1) (x2) (x3)) P_in_place ) ”
  &&  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_3)
  **  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_3)
  **  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_3)
  **  (((&((pt)  # "JPoint" ->ₛ "x" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_3)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3_2)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2_2)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1_2)
  **  (((&((pt)  # "JPoint" ->ₛ "y" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0_2)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (3 * sizeof(UINT64)))) # UInt64  |-> x3)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (2 * sizeof(UINT64)))) # UInt64  |-> x2)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (1 * sizeof(UINT64)))) # UInt64  |-> x1)
  **  (((&((pt)  # "JPoint" ->ₛ "z" .ₛ "v") + (0 * sizeof(UINT64)))) # UInt64  |-> x0)
).

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include array_bridges_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.
Include jpoint_double_trace_Strategy_Correct.

Axiom proof_of_double_JPoint_safety_wit_1_in_place : double_JPoint_safety_wit_1_in_place.
Axiom proof_of_double_JPoint_safety_wit_2_non_alias : double_JPoint_safety_wit_2_non_alias.
Axiom proof_of_double_JPoint_safety_wit_3_in_place : double_JPoint_safety_wit_3_in_place.
Axiom proof_of_double_JPoint_safety_wit_4_non_alias : double_JPoint_safety_wit_4_non_alias.
Axiom proof_of_double_JPoint_entail_wit_1_1_in_place : double_JPoint_entail_wit_1_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_1_2_non_alias : double_JPoint_entail_wit_1_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_2_1_in_place : double_JPoint_entail_wit_2_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_2_2_in_place : double_JPoint_entail_wit_2_2_in_place.
Axiom proof_of_double_JPoint_entail_wit_2_3_non_alias : double_JPoint_entail_wit_2_3_non_alias.
Axiom proof_of_double_JPoint_entail_wit_2_4_non_alias : double_JPoint_entail_wit_2_4_non_alias.
Axiom proof_of_double_JPoint_entail_wit_3_1_in_place : double_JPoint_entail_wit_3_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_3_2_in_place : double_JPoint_entail_wit_3_2_in_place.
Axiom proof_of_double_JPoint_entail_wit_3_3_non_alias : double_JPoint_entail_wit_3_3_non_alias.
Axiom proof_of_double_JPoint_entail_wit_3_4_non_alias : double_JPoint_entail_wit_3_4_non_alias.
Axiom proof_of_double_JPoint_entail_wit_4_1_in_place : double_JPoint_entail_wit_4_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_4_2_non_alias : double_JPoint_entail_wit_4_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_5_1_in_place : double_JPoint_entail_wit_5_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_5_2_non_alias : double_JPoint_entail_wit_5_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_6_1_in_place : double_JPoint_entail_wit_6_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_6_2_non_alias : double_JPoint_entail_wit_6_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_7_1_in_place : double_JPoint_entail_wit_7_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_7_2_non_alias : double_JPoint_entail_wit_7_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_8_1_in_place : double_JPoint_entail_wit_8_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_8_2_non_alias : double_JPoint_entail_wit_8_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_9_1_in_place : double_JPoint_entail_wit_9_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_9_2_non_alias : double_JPoint_entail_wit_9_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_10_1_in_place : double_JPoint_entail_wit_10_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_10_2_non_alias : double_JPoint_entail_wit_10_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_11_1_in_place : double_JPoint_entail_wit_11_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_11_2_non_alias : double_JPoint_entail_wit_11_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_12_1_in_place : double_JPoint_entail_wit_12_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_12_2_non_alias : double_JPoint_entail_wit_12_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_13_1_in_place : double_JPoint_entail_wit_13_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_13_2_non_alias : double_JPoint_entail_wit_13_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_14_1_in_place : double_JPoint_entail_wit_14_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_14_2_non_alias : double_JPoint_entail_wit_14_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_15_1_in_place : double_JPoint_entail_wit_15_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_15_2_non_alias : double_JPoint_entail_wit_15_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_16_1_in_place : double_JPoint_entail_wit_16_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_16_2_non_alias : double_JPoint_entail_wit_16_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_17_1_in_place : double_JPoint_entail_wit_17_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_17_2_non_alias : double_JPoint_entail_wit_17_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_18_1_in_place : double_JPoint_entail_wit_18_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_18_2_non_alias : double_JPoint_entail_wit_18_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_19_1_in_place : double_JPoint_entail_wit_19_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_19_2_non_alias : double_JPoint_entail_wit_19_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_20_1_in_place : double_JPoint_entail_wit_20_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_20_2_non_alias : double_JPoint_entail_wit_20_2_non_alias.
Axiom proof_of_double_JPoint_entail_wit_21_1_in_place : double_JPoint_entail_wit_21_1_in_place.
Axiom proof_of_double_JPoint_entail_wit_21_2_non_alias : double_JPoint_entail_wit_21_2_non_alias.
Axiom proof_of_double_JPoint_return_wit_1_non_alias : double_JPoint_return_wit_1_non_alias.
Axiom proof_of_double_JPoint_return_wit_2_in_place : double_JPoint_return_wit_2_in_place.
Axiom proof_of_double_JPoint_return_wit_3_in_place : double_JPoint_return_wit_3_in_place.
Axiom proof_of_double_JPoint_return_wit_4_non_alias : double_JPoint_return_wit_4_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_1_in_place : double_JPoint_partial_solve_wit_1_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_2_non_alias : double_JPoint_partial_solve_wit_2_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_3_non_alias : double_JPoint_partial_solve_wit_3_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_4_non_alias : double_JPoint_partial_solve_wit_4_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_5_in_place : double_JPoint_partial_solve_wit_5_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_6_in_place : double_JPoint_partial_solve_wit_6_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_7_non_alias : double_JPoint_partial_solve_wit_7_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_8_in_place : double_JPoint_partial_solve_wit_8_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_9_non_alias : double_JPoint_partial_solve_wit_9_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_10_in_place : double_JPoint_partial_solve_wit_10_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_11_non_alias : double_JPoint_partial_solve_wit_11_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_12_in_place_pure : double_JPoint_partial_solve_wit_12_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_12_in_place : double_JPoint_partial_solve_wit_12_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_13_non_alias : double_JPoint_partial_solve_wit_13_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_14_in_place : double_JPoint_partial_solve_wit_14_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_15_non_alias : double_JPoint_partial_solve_wit_15_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_16_in_place : double_JPoint_partial_solve_wit_16_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_17_non_alias : double_JPoint_partial_solve_wit_17_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_18_in_place_pure : double_JPoint_partial_solve_wit_18_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_18_in_place : double_JPoint_partial_solve_wit_18_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_19_non_alias_pure : double_JPoint_partial_solve_wit_19_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_19_non_alias : double_JPoint_partial_solve_wit_19_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_20_in_place : double_JPoint_partial_solve_wit_20_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_21_non_alias : double_JPoint_partial_solve_wit_21_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_22_in_place_pure : double_JPoint_partial_solve_wit_22_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_22_in_place : double_JPoint_partial_solve_wit_22_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_23_non_alias_pure : double_JPoint_partial_solve_wit_23_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_23_non_alias : double_JPoint_partial_solve_wit_23_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_24_in_place_pure : double_JPoint_partial_solve_wit_24_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_24_in_place : double_JPoint_partial_solve_wit_24_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_25_non_alias_pure : double_JPoint_partial_solve_wit_25_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_25_non_alias : double_JPoint_partial_solve_wit_25_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_26_in_place_pure : double_JPoint_partial_solve_wit_26_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_26_in_place : double_JPoint_partial_solve_wit_26_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_27_non_alias_pure : double_JPoint_partial_solve_wit_27_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_27_non_alias : double_JPoint_partial_solve_wit_27_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_28_in_place : double_JPoint_partial_solve_wit_28_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_29_non_alias : double_JPoint_partial_solve_wit_29_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_30_in_place : double_JPoint_partial_solve_wit_30_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_31_non_alias : double_JPoint_partial_solve_wit_31_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_32_in_place_pure : double_JPoint_partial_solve_wit_32_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_32_in_place : double_JPoint_partial_solve_wit_32_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_33_non_alias_pure : double_JPoint_partial_solve_wit_33_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_33_non_alias : double_JPoint_partial_solve_wit_33_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_34_in_place_pure : double_JPoint_partial_solve_wit_34_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_34_in_place : double_JPoint_partial_solve_wit_34_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_35_non_alias_pure : double_JPoint_partial_solve_wit_35_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_35_non_alias : double_JPoint_partial_solve_wit_35_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_36_in_place_pure : double_JPoint_partial_solve_wit_36_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_36_in_place : double_JPoint_partial_solve_wit_36_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_37_non_alias_pure : double_JPoint_partial_solve_wit_37_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_37_non_alias : double_JPoint_partial_solve_wit_37_non_alias.
Axiom proof_of_double_JPoint_partial_solve_wit_38_in_place_pure : double_JPoint_partial_solve_wit_38_in_place_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_38_in_place : double_JPoint_partial_solve_wit_38_in_place.
Axiom proof_of_double_JPoint_partial_solve_wit_39_non_alias_pure : double_JPoint_partial_solve_wit_39_non_alias_pure.
Axiom proof_of_double_JPoint_partial_solve_wit_39_non_alias : double_JPoint_partial_solve_wit_39_non_alias.
Axiom proof_of_double_JPoint_which_implies_wit_1 : double_JPoint_which_implies_wit_1.
Axiom proof_of_double_JPoint_which_implies_wit_2 : double_JPoint_which_implies_wit_2.

End VC_Correct.
