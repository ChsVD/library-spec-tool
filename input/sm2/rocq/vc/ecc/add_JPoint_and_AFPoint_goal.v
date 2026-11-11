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
From SimpleC.EE.Applications_human.sm2.vc.ecc Require Import add_JPoint_and_AFPoint_def.
Import Snaive_C_Rules.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.sm2_common_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.basicOp_lib.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.ecc
      SimpleC.EE.Applications_human.sm2.lib.ecc_scalar_mul.
Require Import
      SimpleC.EE.Applications_human.sm2.lib.add_JPoint_and_AFPoint_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import sm2_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_point_copy_steps_strategy_proof.

(*----- Function add_JPoint_and_AFPoint -----*)

Definition add_JPoint_and_AFPoint_safety_wit_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P1_impl_non_alias = ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_3_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P1_impl_non_alias <> ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_4_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_5_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_non_alias = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_2 = 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_6_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_r_eq_point1 = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval = 0)) (PreH12 : (retval_2 = 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_7_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (P2_impl_non_alias <> ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_2 <> 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_safety_wit_8_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval = 0)) (PreH12 : (retval_2 <> 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ False ”
.

Definition add_JPoint_and_AFPoint_entail_wit_1_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (P1_impl_non_alias = ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval_3 = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_1_2_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P1_impl_non_alias <> ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_1_3_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval_3 = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_1_4_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval_2 = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_2_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P1_impl_non_alias = ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_2_2_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (P1_impl_non_alias <> ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval_3 <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_2_3_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval_2 <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_2_4_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 0)) (PreH4 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval_3 <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_3_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (P1_impl_non_alias = ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (z: Z)  (y: Z)  (x: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z)  (retval_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields point1_pre x_2 y_2 z_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_3_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval_2 <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (z: Z)  (y: Z)  (x: Z)  (retval: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_fields point1_pre x_2 y_2 z_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_4_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_non_alias = ECInfinity)) (PreH7 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH8 : (retval <> 0)) ,
  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (“ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z)  (retval_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UndefStructPredJPoint result_pre )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_4_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_2: Z) (x_2: Z) (y_2: Z) (z_2: Z) (PreH1 : (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 1)) (PreH6 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH7 : (result_pre = point1_pre)) (PreH8 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH9 : (retval_2 <> 0)) ,
  (store_jpoint_fields point1_pre x_2 y_2 z_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (z: Z)  (y: Z)  (x: Z)  (retval: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UndefStructPredJPoint result_pre )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_5_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_non_alias = ECInfinity)) (PreH7 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH8 : (retval <> 0)) ,
  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (“ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z)  (retval_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "z") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_5_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_2: Z) (x_2: Z) (y_2: Z) (z_2: Z) (PreH1 : (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 1)) (PreH6 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH7 : (result_pre = point1_pre)) (PreH8 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH9 : (retval_2 <> 0)) ,
  (UndefStructPredJPoint result_pre )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (z: Z)  (y: Z)  (x: Z)  (retval: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "z") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_6_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (P2_impl_non_alias = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_5 = 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_6_2_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (P2_impl_non_alias <> ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_2 = 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_6_3_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 1)) (PreH4 : (P2_impl_r_eq_point1 = ECInfinity)) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 <= 1)) (PreH7 : (retval_3 = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_5 = 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_6_4_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 <= 1)) (PreH7 : (retval_3 = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_4 = 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_7_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_non_alias = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_2 <> 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P2_impl_non_alias = ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (P2_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_7_2_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (P2_impl_non_alias <> ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_5 <> 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P2_impl_non_alias = ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_4: Z)  (retval_3: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (P2_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_7_3_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 1)) (PreH4 : (P2_impl_r_eq_point1 = ECInfinity)) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 <= 1)) (PreH7 : (retval_3 = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_4 <> 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P2_impl_non_alias = ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (P2_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_7_4_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (retval_5: Z) (PreH1 : (0 <= retval_5)) (PreH2 : (retval_5 <= 1)) (PreH3 : (retval_5 = 0)) (PreH4 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 <= 1)) (PreH7 : (retval_3 = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_5 <> 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (retval_2: Z)  (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P2_impl_non_alias = ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (retval_4: Z) ,
  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (P2_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_8_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (P2_impl_non_alias <> ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_2 = 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (z: Z)  (y: Z)  (x: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z)  (retval_4: Z)  (retval_3: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_jpoint_fields point1_pre x_2 y_2 z_2 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_8_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (retval_4: Z) (PreH1 : (0 <= retval_4)) (PreH2 : (retval_4 <= 1)) (PreH3 : (retval_4 = 0)) (PreH4 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (0 <= retval_3)) (PreH6 : (retval_3 <= 1)) (PreH7 : (retval_3 = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval_3 = 0)) (PreH12 : (retval_4 = 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (z: Z)  (y: Z)  (x: Z)  (retval_2: Z)  (retval: Z) ,
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_jpoint_fields point1_pre x y z )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (z_2: Z)  (y_2: Z)  (x_2: Z) ,
  “ (jpoint_canonical_infinity_encoding x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_2 y_2 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_jpoint_fields point1_pre x_2 y_2 z_2 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_9_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 <= 1)) (PreH5 : (retval_2 = 0)) (PreH6 : (P2_impl_non_alias <> ECInfinity)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 0)) (PreH10 : (P1_impl_non_alias <> ECInfinity)) (PreH11 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH12 : (retval = 0)) (PreH13 : (retval_2 = 0)) ,
  (store_jpoint_fields point1_pre x y z )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (y_2: Z)  (x_2: Z) ,
  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (y_4: Z)  (x_4: Z)  (z_2: Z)  (y_3: Z)  (x_3: Z)  (retval_4: Z)  (retval_3: Z) ,
  “ (afpoint_represents x_4 y_4 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x_3 y_3 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_3 y_3 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint_fields point2_pre x_4 y_4 )
  **  (store_jpoint_fields point1_pre x_3 y_3 z_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_entail_wit_9_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval_3: Z) (retval_4: Z) (x_3: Z) (y_3: Z) (z_2: Z) (PreH1 : (jpoint_canonical_infinity_encoding x_3 y_3 z_2 P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x_3 y_3 z_2 P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval_4)) (PreH4 : (retval_4 <= 1)) (PreH5 : (retval_4 = 0)) (PreH6 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH7 : (0 <= retval_3)) (PreH8 : (retval_3 <= 1)) (PreH9 : (retval_3 = 0)) (PreH10 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH11 : (result_pre = point1_pre)) (PreH12 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH13 : (retval_3 = 0)) (PreH14 : (retval_4 = 0)) ,
  (store_jpoint_fields point1_pre x_3 y_3 z_2 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (EX (y_2: Z)  (x_2: Z)  (z: Z)  (y: Z)  (x: Z)  (retval_2: Z)  (retval: Z) ,
  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (store_jpoint_fields point1_pre x y z )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (EX (y_4: Z)  (x_4: Z) ,
  “ (afpoint_represents x_4 y_4 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x_3 y_3 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x_3 y_3 z_2 P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_4) ” 
  &&  “ (retval_4 <= 1) ” 
  &&  “ (retval_4 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 1) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ (retval_4 = 0) ”
  &&  (store_afpoint_fields point2_pre x_4 y_4 )
  **  (store_jpoint_fields point1_pre x_3 y_3 z_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
.

Definition add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1 := 
(
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_r_eq_point1 = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval = 0)) (PreH12 : (retval_2 <> 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (result_pre = point1_pre) ”
  &&  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
) \/
(
forall (result_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_r_eq_point1 = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval = 0)) (PreH12 : (retval_2 <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
|--
  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
).

Definition add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1_split_goal_spatial := 
forall (result_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_r_eq_point1 = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH9 : (result_pre = point1_pre)) (PreH10 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH11 : (retval = 0)) (PreH12 : (retval_2 <> 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
|--
  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias := 
(
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((point1_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((point1_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
  **  (UInt64Array.full &((point1_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
) \/
(
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (0 <= JZ) ” 
  &&  “ (JZ < SM2_P_Z) ” 
  &&  “ (0 <= JY) ” 
  &&  “ (JY < SM2_P_Z) ” 
  &&  “ (0 <= JX) ” 
  &&  “ (JX < SM2_P_Z) ”
  &&  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
).

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_1 := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (0 <= JZ) ”
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_2 := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (JZ < SM2_P_Z) ”
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_3 := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (0 <= JY) ”
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_4 := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (JY < SM2_P_Z) ”
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_5 := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (0 <= JX) ”
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_6 := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  “ (JX < SM2_P_Z) ”
.

Definition add_JPoint_and_AFPoint_return_wit_2_impl_non_alias_split_goal_spatial := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
|--
  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
.

Definition add_JPoint_and_AFPoint_return_wit_3_impl_non_alias := 
(
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_non_alias = ECInfinity)) (PreH7 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH8 : (retval <> 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre P2_impl_non_alias )
  **  (store_jpoint_zero )
  **  (store_jpoint_fields point1_pre x y z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
) \/
(
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_non_alias = ECInfinity)) (PreH7 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH8 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity result_pre P2_impl_non_alias )
|--
  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
).

Definition add_JPoint_and_AFPoint_return_wit_3_impl_non_alias_split_goal_spatial := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_non_alias = ECInfinity)) (PreH7 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH8 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity result_pre P2_impl_non_alias )
|--
  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
.

Definition add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1 := 
(
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH7 : (result_pre = point1_pre)) (PreH8 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH9 : (retval <> 0)) ,
  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity result_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (result_pre = point1_pre) ”
  &&  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
) \/
(
forall (result_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH7 : (result_pre = point1_pre)) (PreH8 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH9 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity result_pre P2_impl_r_eq_point1 )
|--
  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
).

Definition add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1_split_goal_spatial := 
forall (result_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH7 : (result_pre = point1_pre)) (PreH8 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH9 : (retval <> 0)) ,
  (store_jpoint_with_canonical_infinity result_pre P2_impl_r_eq_point1 )
|--
  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
.

Definition add_JPoint_and_AFPoint_return_wit_5_impl_non_alias := 
(
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod ((z * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
|--
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
) \/
(
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod ((z * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
|--
  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
).

Definition add_JPoint_and_AFPoint_return_wit_5_impl_non_alias_split_goal_spatial := 
forall (result_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod ((z * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
|--
  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
.

Definition add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1 := 
(
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((point1_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod ((z * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
|--
  “ (result_pre = point1_pre) ”
  &&  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
) \/
(
forall (result_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((point1_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod ((z * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
|--
  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
).

Definition add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1_split_goal_spatial := 
forall (result_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "z") = &((point1_pre)  # "JPoint" ->ₛ "z"))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "z") (Zmod ((z * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
|--
  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_1_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (PreH1 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_2_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (PreH1 : (result_pre = point1_pre)) (PreH2 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_3_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH2 : (jpoint_represents x y z P1_impl_non_alias )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_non_alias = ECInfinity)) (PreH7 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH8 : (retval <> 0)) ,
  (store_jpoint_fields point1_pre x y z )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_non_alias = ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
  **  (store_jpoint_fields point1_pre x y z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_4_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (x: Z) (y: Z) (z: Z) (PreH1 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH2 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH3 : (0 <= retval)) (PreH4 : (retval <= 1)) (PreH5 : (retval = 1)) (PreH6 : (P1_impl_r_eq_point1 = ECInfinity)) (PreH7 : (result_pre = point1_pre)) (PreH8 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH9 : (retval <> 0)) ,
  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "z") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "y") )
  **  (UndefStructPredu32 &((result_pre)  # "JPoint" ->ₛ "x") )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P1_impl_r_eq_point1 = ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval <> 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_5_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P1_impl_non_alias <> ECInfinity)) (PreH5 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH6 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_6_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH5 : (result_pre = point1_pre)) (PreH6 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH7 : (retval = 0)) ,
  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_7_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (P2_impl_non_alias = ECInfinity)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (P1_impl_non_alias <> ECInfinity)) (PreH9 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH10 : (retval = 0)) (PreH11 : (retval_2 <> 0)) ,
  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P2_impl_non_alias = ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_8_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (z_limbs: (@list Z)) (y_limbs: (@list Z)) (x_limbs: (@list Z)) (JX: Z) (JY: Z) (JZ: Z) (PreH1 : (jpoint_represents JX JY JZ P1_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias )) (PreH3 : ((Zlength (x_limbs)) = 4)) (PreH4 : (u64_list_bounded x_limbs )) (PreH5 : ((u64_list_value (x_limbs)) = JX)) (PreH6 : ((Zlength (y_limbs)) = 4)) (PreH7 : (u64_list_bounded y_limbs )) (PreH8 : ((u64_list_value (y_limbs)) = JY)) (PreH9 : ((Zlength (z_limbs)) = 4)) (PreH10 : (u64_list_bounded z_limbs )) (PreH11 : ((u64_list_value (z_limbs)) = JZ)) (PreH12 : (0 <= retval_2)) (PreH13 : (retval_2 <= 1)) (PreH14 : (retval_2 = 1)) (PreH15 : (P2_impl_non_alias = ECInfinity)) (PreH16 : (0 <= retval)) (PreH17 : (retval <= 1)) (PreH18 : (retval = 0)) (PreH19 : (P1_impl_non_alias <> ECInfinity)) (PreH20 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH21 : (retval = 0)) (PreH22 : (retval_2 <> 0)) ,
  (UndefStructPredJPoint result_pre )
  **  (StructPredJPoint point1_pre (make_record_jpoint ((make_record_u32 (x_limbs))) ((make_record_u32 (y_limbs))) ((make_record_u32 (z_limbs)))) )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (jpoint_represents JX JY JZ P1_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias ) ” 
  &&  “ ((Zlength (x_limbs)) = 4) ” 
  &&  “ (u64_list_bounded x_limbs ) ” 
  &&  “ ((u64_list_value (x_limbs)) = JX) ” 
  &&  “ ((Zlength (y_limbs)) = 4) ” 
  &&  “ (u64_list_bounded y_limbs ) ” 
  &&  “ ((u64_list_value (y_limbs)) = JY) ” 
  &&  “ ((Zlength (z_limbs)) = 4) ” 
  &&  “ (u64_list_bounded z_limbs ) ” 
  &&  “ ((u64_list_value (z_limbs)) = JZ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (P2_impl_non_alias = ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 <> 0) ”
  &&  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (UInt64Array.full &((point1_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 z_limbs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.full &((point1_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 y_limbs )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.full &((point1_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 x_limbs )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_9_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH3 : (jpoint_represents x y z P1_impl_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P2_impl_non_alias <> ECInfinity)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 0)) (PreH11 : (P1_impl_non_alias <> ECInfinity)) (PreH12 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UndefStructPredu32 ( &( "z2" ) ) )
  **  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (store_jpoint_fields point1_pre x y z )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (UInt64Array.undef_full &(( &( "z2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_10_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH2 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH3 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 0)) (PreH11 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (result_pre = point1_pre)) (PreH13 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH14 : (retval = 0)) (PreH15 : (retval_2 = 0)) ,
  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (UndefStructPredu32 ( &( "z2" ) ) )
  **  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (store_jpoint_fields point1_pre x y z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (UInt64Array.undef_full &(( &( "z2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_11_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH2 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH3 : (jpoint_represents x y z P1_impl_non_alias )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P2_impl_non_alias <> ECInfinity)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 0)) (PreH11 : (P1_impl_non_alias <> ECInfinity)) (PreH12 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH13 : (retval = 0)) (PreH14 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "A" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_12_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH2 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH3 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH4 : (0 <= retval_2)) (PreH5 : (retval_2 <= 1)) (PreH6 : (retval_2 = 0)) (PreH7 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH8 : (0 <= retval)) (PreH9 : (retval <= 1)) (PreH10 : (retval = 0)) (PreH11 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (result_pre = point1_pre)) (PreH13 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH14 : (retval = 0)) (PreH15 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UndefStructPredu32 ( &( "A" ) ) )
  **  (store_afpoint_fields point2_pre x_2 y_2 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "A" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_13_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "B" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_14_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UndefStructPredu32 ( &( "B" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "B" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias := add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias_pure -> add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "A" ) ) = ( &( "A" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "A" ) ) = ( &( "A" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias := add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias_pure -> add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (( &( "A" ) ) = ( &( "A" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
|--
  “ (( &( "A" ) ) = ( &( "A" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "A" ) ) (Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "A" ) ) = ( &( "A" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "A" ) ) = ( &( "A" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias := add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias_pure -> add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "A" ) ) = ( &( "A" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "A" ) ) = ( &( "A" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_21_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "C2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_22_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_sm2_p )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_sm2_rhop )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UndefStructPredu32 ( &( "C2" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "C2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_23_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "C3" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_24_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UndefStructPredu32 ( &( "C3" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "C3" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_25_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "X1C2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_26_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UndefStructPredu32 ( &( "X1C2" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "X1C2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_27_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "D2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_28_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UndefStructPredu32 ( &( "D2" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "D2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "X1C2" ) ) = ( &( "X1C2" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "X1C2" ) ) = ( &( "X1C2" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "X1C22" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias := add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias_pure -> add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (( &( "X1C2" ) ) = ( &( "X1C2" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UndefStructPredu32 ( &( "X1C22" ) ) )
  **  (store_jpoint_zero )
|--
  “ (( &( "X1C2" ) ) = ( &( "X1C2" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "X1C22" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_31_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "X1C2" ) ) = ( &( "X1C2" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_32_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "X1C2" ) ) = ( &( "X1C2" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias := add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias_pure -> add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (store_jpoint_zero )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x")) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_35_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_36_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (&((result_pre)  # "JPoint" ->ₛ "x") = &((result_pre)  # "JPoint" ->ₛ "x"))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UndefStructPredu32 ( &( "tmp" ) ) )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias := add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias_pure -> add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
|--
  “ (( &( "B" ) ) = ( &( "B" ) )) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_partial_solve_wit_39_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH8 : (jpoint_represents x y z P1_impl_non_alias )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_non_alias <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_non_alias <> ECInfinity)) (PreH17 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_40_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (( &( "B" ) ) = ( &( "B" ) ))) (PreH2 : (y_2 < SM2_P_Z)) (PreH3 : (0 <= y_2)) (PreH4 : (x_2 < SM2_P_Z)) (PreH5 : (0 <= x_2)) (PreH6 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH7 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH8 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 <= 1)) (PreH11 : (retval_2 = 0)) (PreH12 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH13 : (0 <= retval)) (PreH14 : (retval <= 1)) (PreH15 : (retval = 0)) (PreH16 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH17 : (result_pre = point1_pre)) (PreH18 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH19 : (retval = 0)) (PreH20 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "tmp" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_41_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_42_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_43_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_non_alias: ec_point) (P1_impl_non_alias: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_non_alias )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias )) (PreH7 : (jpoint_represents x y z P1_impl_non_alias )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_non_alias <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_non_alias <> ECInfinity)) (PreH16 : (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias))) (PreH17 : (retval = 0)) (PreH18 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_non_alias ) ” 
  &&  “ (jpoint_represents x y z P1_impl_non_alias ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_non_alias <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_non_alias <> ECInfinity) ” 
  &&  “ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "y") y )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "x") x )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1_pure := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  ((( &( "point1" ) )) # Ptr  |-> point1_pre)
  **  ((( &( "point2" ) )) # Ptr  |-> point2_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (store_jpoint_zero )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((point1_pre)  # "JPoint" ->ₛ "z")) ”
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1_aux := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_impl_r_eq_point1: ec_point) (P1_impl_r_eq_point1: ec_point) (retval: Z) (retval_2: Z) (x: Z) (y: Z) (z: Z) (x_2: Z) (y_2: Z) (PreH1 : (y_2 < SM2_P_Z)) (PreH2 : (0 <= y_2)) (PreH3 : (x_2 < SM2_P_Z)) (PreH4 : (0 <= x_2)) (PreH5 : (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 )) (PreH6 : (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 )) (PreH7 : (jpoint_represents x y z P1_impl_r_eq_point1 )) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 <= 1)) (PreH10 : (retval_2 = 0)) (PreH11 : (P2_impl_r_eq_point1 <> ECInfinity)) (PreH12 : (0 <= retval)) (PreH13 : (retval <= 1)) (PreH14 : (retval = 0)) (PreH15 : (P1_impl_r_eq_point1 <> ECInfinity)) (PreH16 : (result_pre = point1_pre)) (PreH17 : (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1))) (PreH18 : (retval = 0)) (PreH19 : (retval_2 = 0)) ,
  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
|--
  “ (&((result_pre)  # "JPoint" ->ₛ "z") = &((point1_pre)  # "JPoint" ->ₛ "z")) ” 
  &&  “ (y_2 < SM2_P_Z) ” 
  &&  “ (0 <= y_2) ” 
  &&  “ (x_2 < SM2_P_Z) ” 
  &&  “ (0 <= x_2) ” 
  &&  “ (afpoint_represents x_2 y_2 P2_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_canonical_infinity_encoding x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (jpoint_represents x y z P1_impl_r_eq_point1 ) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (P2_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P1_impl_r_eq_point1 <> ECInfinity) ” 
  &&  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp &((point1_pre)  # "JPoint" ->ₛ "z") z )
  **  (store_fp ( &( "A" ) ) (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "B" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "tmp" ) ) (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "y") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod ((y * (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C3" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C2" ) ) (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((result_pre)  # "JPoint" ->ₛ "x") (Zmod (((Zmod (((Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) - (Zmod (((Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "D2" ) ) (Zmod (((Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) * (Zmod (((Zmod (((Zmod ((y_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) * z )) (SM2_P_Z)) - y )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "X1C22" ) ) (Zmod (((Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((x * (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "C2" ) ) (Zmod (((Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) * (Zmod (((Zmod ((x_2 * (Zmod ((z * z )) (SM2_P_Z)) )) (SM2_P_Z)) - x )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "y") y_2 )
  **  (store_fp ( &( "z2" ) ) (Zmod ((z * z )) (SM2_P_Z)) )
  **  (store_fp &((point2_pre)  # "AFPoint" ->ₛ "x") x_2 )
  **  (store_jpoint_zero )
.

Definition add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1 := add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1_pure -> add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1_aux.

Definition add_JPoint_and_AFPoint_which_implies_wit_1 := 
(
forall (P1_impl_non_alias: ec_point) (point1: Z) (result: Z) ,
  (store_jpoint_with_canonical_infinity point1 P1_impl_non_alias )
  **  (UInt64Array.undef_full &((result)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
|--
  EX (z_limbs: (@list Z))  (y_limbs: (@list Z))  (x_limbs: (@list Z))  (JX: Z)  (JY: Z)  (JZ: Z) ,
  “ (jpoint_represents JX JY JZ P1_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding JX JY JZ P1_impl_non_alias ) ” 
  &&  “ ((Zlength (x_limbs)) = 4) ” 
  &&  “ (u64_list_bounded x_limbs ) ” 
  &&  “ ((u64_list_value (x_limbs)) = JX) ” 
  &&  “ ((Zlength (y_limbs)) = 4) ” 
  &&  “ (u64_list_bounded y_limbs ) ” 
  &&  “ ((u64_list_value (y_limbs)) = JY) ” 
  &&  “ ((Zlength (z_limbs)) = 4) ” 
  &&  “ (u64_list_bounded z_limbs ) ” 
  &&  “ ((u64_list_value (z_limbs)) = JZ) ”
  &&  (StructPredJPoint point1 (make_record_jpoint ((make_record_u32 (x_limbs))) ((make_record_u32 (y_limbs))) ((make_record_u32 (z_limbs)))) )
  **  (UndefStructPredJPoint result )
) \/
(
forall (P1_impl_non_alias: ec_point) (point1: Z) ,
  (store_jpoint_with_canonical_infinity point1 P1_impl_non_alias )
|--
  EX (z_limbs: (@list Z))  (y_limbs: (@list Z))  (x_limbs: (@list Z)) ,
  “ (jpoint_represents (u64_list_value (x_limbs)) (u64_list_value (y_limbs)) (u64_list_value (z_limbs)) P1_impl_non_alias ) ” 
  &&  “ (jpoint_canonical_infinity_encoding (u64_list_value (x_limbs)) (u64_list_value (y_limbs)) (u64_list_value (z_limbs)) P1_impl_non_alias ) ” 
  &&  “ ((Zlength (x_limbs)) = 4) ” 
  &&  “ (u64_list_bounded x_limbs ) ” 
  &&  “ ((Zlength (y_limbs)) = 4) ” 
  &&  “ (u64_list_bounded y_limbs ) ” 
  &&  “ ((Zlength (z_limbs)) = 4) ” 
  &&  “ (u64_list_bounded z_limbs ) ”
  &&  (StructPredJPoint point1 (make_record_jpoint ((make_record_u32 (x_limbs))) ((make_record_u32 (y_limbs))) ((make_record_u32 (z_limbs)))) )
).

Definition add_JPoint_and_AFPoint_derive_canonical_r_eq_point1_by_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_canonical_r_eq_point1: ec_point) (P1_canonical_r_eq_point1: ec_point) ,
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_r_eq_point1 <> ECInfinity) /\ (P2_canonical_r_eq_point1 <> ECInfinity)) -> (P1_canonical_r_eq_point1 <> P2_canonical_r_eq_point1)) ” 
  &&  “ (P1_canonical_r_eq_point1 = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_r_eq_point1 <> ECInfinity) /\ (P2_canonical_r_eq_point1 <> ECInfinity)) -> (P1_canonical_r_eq_point1 <> P2_canonical_r_eq_point1)) ” 
  &&  “ (P2_canonical_r_eq_point1 = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_canonical_r_eq_point1 <> ECInfinity) /\ (P2_canonical_r_eq_point1 <> ECInfinity)) -> (P1_canonical_r_eq_point1 <> P2_canonical_r_eq_point1)) ” 
  &&  “ ((sm2_point_add (P1_canonical_r_eq_point1) (P2_canonical_r_eq_point1)) <> ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_r_eq_point1 )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
|--
EX (P1_impl_r_eq_point1: ec_point) (P2_impl_r_eq_point1: ec_point) ,
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  **
  ((“ (result_pre = point1_pre) ”
  &&  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  -*
  (“ (result_pre = point1_pre) ”
  &&  (store_jpoint_with_canonical_infinity result_pre (sm2_point_add (P1_canonical_r_eq_point1) (P2_canonical_r_eq_point1)) )
  **  (store_afpoint point2_pre P2_canonical_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )))
.

Definition add_JPoint_and_AFPoint_derive_r_eq_point1_by_impl_r_eq_point1 := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_r_eq_point1: ec_point) (P1_r_eq_point1: ec_point) ,
  “ (result_pre = point1_pre) ” 
  &&  “ (((P1_r_eq_point1 <> ECInfinity) /\ (P2_r_eq_point1 <> ECInfinity)) -> (P1_r_eq_point1 <> P2_r_eq_point1)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_r_eq_point1 )
  **  (store_afpoint point2_pre P2_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
EX (P1_impl_r_eq_point1: ec_point) (P2_impl_r_eq_point1: ec_point) ,
  (“ (result_pre = point1_pre) ” 
  &&  “ (((P1_impl_r_eq_point1 <> ECInfinity) /\ (P2_impl_r_eq_point1 <> ECInfinity)) -> (P1_impl_r_eq_point1 <> P2_impl_r_eq_point1)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  **
  ((“ (result_pre = point1_pre) ”
  &&  (store_mixed_add_result_impl result_pre P1_impl_r_eq_point1 P2_impl_r_eq_point1 )
  **  (store_afpoint point2_pre P2_impl_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  -*
  (“ (result_pre = point1_pre) ”
  &&  (store_jpoint result_pre (sm2_point_add (P1_r_eq_point1) (P2_r_eq_point1)) )
  **  (store_afpoint point2_pre P2_r_eq_point1 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )))
.

Definition add_JPoint_and_AFPoint_derive_canonical_non_alias_by_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_canonical_non_alias: ec_point) (P1_canonical_non_alias: ec_point) ,
  (“ (((P1_canonical_non_alias <> ECInfinity) /\ (P2_canonical_non_alias <> ECInfinity)) -> (P1_canonical_non_alias <> P2_canonical_non_alias)) ” 
  &&  “ (P1_canonical_non_alias = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_non_alias )
  **  (store_afpoint point2_pre P2_canonical_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (((P1_canonical_non_alias <> ECInfinity) /\ (P2_canonical_non_alias <> ECInfinity)) -> (P1_canonical_non_alias <> P2_canonical_non_alias)) ” 
  &&  “ (P2_canonical_non_alias = ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_non_alias )
  **  (store_afpoint point2_pre P2_canonical_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  ||
  (“ (((P1_canonical_non_alias <> ECInfinity) /\ (P2_canonical_non_alias <> ECInfinity)) -> (P1_canonical_non_alias <> P2_canonical_non_alias)) ” 
  &&  “ ((sm2_point_add (P1_canonical_non_alias) (P2_canonical_non_alias)) <> ECInfinity) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_canonical_non_alias )
  **  (store_afpoint point2_pre P2_canonical_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
|--
EX (P1_impl_non_alias: ec_point) (P2_impl_non_alias: ec_point) ,
  (“ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  **
  (((store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  -*
  ((store_jpoint_with_canonical_infinity point1_pre P1_canonical_non_alias )
  **  (store_afpoint point2_pre P2_canonical_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre (sm2_point_add (P1_canonical_non_alias) (P2_canonical_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )))
.

Definition add_JPoint_and_AFPoint_derive_non_alias_by_impl_non_alias := 
forall (result_pre: Z) (point2_pre: Z) (point1_pre: Z) (P2_non_alias: ec_point) (P1_non_alias: ec_point) ,
  “ (((P1_non_alias <> ECInfinity) /\ (P2_non_alias <> ECInfinity)) -> (P1_non_alias <> P2_non_alias)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_non_alias )
  **  (store_afpoint point2_pre P2_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )
|--
EX (P1_impl_non_alias: ec_point) (P2_impl_non_alias: ec_point) ,
  (“ (((P1_impl_non_alias <> ECInfinity) /\ (P2_impl_non_alias <> ECInfinity)) -> (P1_impl_non_alias <> P2_impl_non_alias)) ”
  &&  (store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  **
  (((store_jpoint_with_canonical_infinity point1_pre P1_impl_non_alias )
  **  (store_afpoint point2_pre P2_impl_non_alias )
  **  (store_mixed_add_result_impl result_pre P1_impl_non_alias P2_impl_non_alias )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero ))
  -*
  ((store_jpoint_with_canonical_infinity point1_pre P1_non_alias )
  **  (store_afpoint point2_pre P2_non_alias )
  **  (store_jpoint result_pre (sm2_point_add (P1_non_alias) (P2_non_alias)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_jpoint_zero )))
.

Definition affine_to_jacobian_derive_point_non_alias_by_non_alias := 
forall (result_pre: Z) (point_pre: Z) (P_point_non_alias: ec_point) ,
  (store_afpoint point_pre P_point_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero )
|--
EX (X_non_alias: Z) (Y_non_alias: Z) ,
  ((store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((result_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_jpoint_zero ))
  **
  ((EX RX RY RZ,
  “ (afpoint_to_jpoint_coordinates X_non_alias Y_non_alias RX RY RZ ) ”
  &&  (store_afpoint_fields point_pre X_non_alias Y_non_alias )
  **  (store_jpoint_fields result_pre RX RY RZ )
  **  (store_jpoint_zero ))
  -*
  ((store_afpoint point_pre P_point_non_alias )
  **  (store_jpoint_with_canonical_infinity result_pre P_point_non_alias )
  **  (store_jpoint_zero )))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.
Include ecc_point_copy_steps_Strategy_Correct.

Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_1_impl_non_alias : add_JPoint_and_AFPoint_safety_wit_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_safety_wit_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_3_impl_non_alias : add_JPoint_and_AFPoint_safety_wit_3_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_safety_wit_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_5_impl_non_alias : add_JPoint_and_AFPoint_safety_wit_5_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_6_impl_r_eq_point1 : add_JPoint_and_AFPoint_safety_wit_6_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_7_impl_non_alias : add_JPoint_and_AFPoint_safety_wit_7_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_safety_wit_8_impl_r_eq_point1 : add_JPoint_and_AFPoint_safety_wit_8_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_1_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_1_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_1_2_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_1_2_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_1_3_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_1_3_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_1_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_1_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_2_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_2_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_2_2_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_2_2_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_2_3_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_2_3_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_2_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_2_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_3_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_3_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_3_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_3_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_4_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_4_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_4_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_4_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_5_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_5_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_5_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_5_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_6_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_6_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_6_2_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_6_2_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_6_3_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_6_3_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_6_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_6_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_7_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_7_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_7_2_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_7_2_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_7_3_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_7_3_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_7_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_7_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_8_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_8_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_8_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_8_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_9_1_impl_non_alias : add_JPoint_and_AFPoint_entail_wit_9_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_entail_wit_9_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_entail_wit_9_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1 : add_JPoint_and_AFPoint_return_wit_1_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_return_wit_2_impl_non_alias : add_JPoint_and_AFPoint_return_wit_2_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_return_wit_3_impl_non_alias : add_JPoint_and_AFPoint_return_wit_3_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_return_wit_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_return_wit_5_impl_non_alias : add_JPoint_and_AFPoint_return_wit_5_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1 : add_JPoint_and_AFPoint_return_wit_6_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_1_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_1_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_2_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_2_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_3_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_3_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_4_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_4_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_5_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_5_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_6_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_6_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_7_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_7_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_8_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_8_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_9_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_9_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_10_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_10_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_11_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_11_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_12_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_12_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_13_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_13_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_14_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_14_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias_pure : add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_15_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_16_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias_pure : add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_17_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_18_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias_pure : add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_19_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_20_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_21_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_21_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_22_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_22_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_23_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_23_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_24_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_24_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_25_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_25_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_26_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_26_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_27_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_27_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_28_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_28_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias_pure : add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_29_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_30_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_31_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_31_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_32_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_32_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias_pure : add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_33_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_34_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_35_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_35_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_36_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_36_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias_pure : add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_37_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_38_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_39_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_39_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_40_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_40_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_41_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_41_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_42_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_42_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_43_impl_non_alias : add_JPoint_and_AFPoint_partial_solve_wit_43_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1_pure : add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1_pure.
Axiom proof_of_add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1 : add_JPoint_and_AFPoint_partial_solve_wit_44_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_which_implies_wit_1 : add_JPoint_and_AFPoint_which_implies_wit_1.
Axiom proof_of_add_JPoint_and_AFPoint_derive_canonical_r_eq_point1_by_impl_r_eq_point1 : add_JPoint_and_AFPoint_derive_canonical_r_eq_point1_by_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_derive_r_eq_point1_by_impl_r_eq_point1 : add_JPoint_and_AFPoint_derive_r_eq_point1_by_impl_r_eq_point1.
Axiom proof_of_add_JPoint_and_AFPoint_derive_canonical_non_alias_by_impl_non_alias : add_JPoint_and_AFPoint_derive_canonical_non_alias_by_impl_non_alias.
Axiom proof_of_add_JPoint_and_AFPoint_derive_non_alias_by_impl_non_alias : add_JPoint_and_AFPoint_derive_non_alias_by_impl_non_alias.
Axiom proof_of_affine_to_jacobian_derive_point_non_alias_by_non_alias : affine_to_jacobian_derive_point_non_alias_by_non_alias.

End VC_Correct.
