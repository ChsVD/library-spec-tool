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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_constants_strategy_proof.

(*----- Function is_on_curve -----*)

Definition is_on_curve_safety_wit_1 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval = 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition is_on_curve_safety_wit_2 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (Y <> 0)) (PreH5 : (retval <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition is_on_curve_safety_wit_3 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X <> 0)) (PreH5 : (retval <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ False ”
.

Definition is_on_curve_safety_wit_4 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_on_curve_entail_wit_1_1 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval_3: Z) (PreH1 : (0 <= retval_3)) (PreH2 : (retval_3 <= 1)) (PreH3 : (retval_3 = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval_3 = 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition is_on_curve_entail_wit_1_2 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (Y <> 0)) (PreH5 : (retval = 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (EX (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition is_on_curve_entail_wit_1_3 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (X <> 0)) (PreH5 : (retval_2 = 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop ))
.

Definition is_on_curve_entail_wit_2_1 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X = 0) ” 
  &&  “ (Y = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition is_on_curve_entail_wit_2_2 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (Y <> 0)) (PreH5 : (retval_2 <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X = 0) ” 
  &&  “ (Y = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition is_on_curve_entail_wit_2_3 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (X <> 0)) (PreH5 : (retval_2 <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  EX (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X = 0) ” 
  &&  “ (Y = 0) ” 
  &&  “ (retval <> 0) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition is_on_curve_entail_wit_3_1 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (( &( "x3" ) ) = ( &( "x3" ) ))) (PreH2 : (Y < SM2_P_Z)) (PreH3 : (0 <= Y)) (PreH4 : (X < SM2_P_Z)) (PreH5 : (0 <= X)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (Y <> 0)) (PreH10 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  (“ (( &( "x3" ) ) = ( &( "x3" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_b ))
  ||
  (EX (retval_2: Z) ,
  “ (( &( "x3" ) ) = ( &( "x3" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_b ))
.

Definition is_on_curve_entail_wit_3_2 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (PreH1 : (( &( "x3" ) ) = ( &( "x3" ) ))) (PreH2 : (Y < SM2_P_Z)) (PreH3 : (0 <= Y)) (PreH4 : (X < SM2_P_Z)) (PreH5 : (0 <= X)) (PreH6 : (0 <= retval_2)) (PreH7 : (retval_2 <= 1)) (PreH8 : (retval_2 = 0)) (PreH9 : (X <> 0)) (PreH10 : (retval_2 = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  (EX (retval: Z) ,
  “ (( &( "x3" ) ) = ( &( "x3" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_b ))
  ||
  (“ (( &( "x3" ) ) = ( &( "x3" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_b ))
.

Definition is_on_curve_entail_wit_4_1 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_b )
|--
  (“ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre))
  ||
  (EX (retval_2: Z) ,
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre))
.

Definition is_on_curve_entail_wit_4_2 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 1)) (PreH7 : (retval_2 = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval_2 = 0)) ,
  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_b )
|--
  (EX (retval: Z) ,
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre))
  ||
  (“ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre))
.

Definition is_on_curve_return_wit_1 := 
(
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) = (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (Y <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint X Y ) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) = (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (Y <> 0)) (PreH17 : (retval_2 = 0)) ,
  TT && emp 
|--
  “ (valid_afpoint X Y ) ”
  &&  emp
).

Definition is_on_curve_return_wit_1_split_goal_1 := 
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) = (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (Y <> 0)) (PreH17 : (retval_2 = 0)) ,
  (valid_afpoint X Y )
.

Definition is_on_curve_return_wit_2 := 
(
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) <> (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (Y <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((valid_afpoint X Y )) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) <> (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (Y <> 0)) (PreH17 : (retval_2 = 0)) ,
  TT && emp 
|--
  “ ~((valid_afpoint X Y )) ”
  &&  emp
).

Definition is_on_curve_return_wit_2_split_goal_1 := 
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) <> (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (Y <> 0)) (PreH17 : (retval_2 = 0)) ,
  ~((valid_afpoint X Y ))
.

Definition is_on_curve_return_wit_3 := 
(
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) = (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (X <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (valid_afpoint X Y ) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) = (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (X <> 0)) (PreH17 : (retval_2 = 0)) ,
  TT && emp 
|--
  “ (valid_afpoint X Y ) ”
  &&  emp
).

Definition is_on_curve_return_wit_3_split_goal_1 := 
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) = (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (X <> 0)) (PreH17 : (retval_2 = 0)) ,
  (valid_afpoint X Y )
.

Definition is_on_curve_return_wit_4 := 
(
forall (point_pre: Z) (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) <> (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (X <> 0)) (PreH17 : (retval_2 = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
|--
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((valid_afpoint X Y )) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) <> (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (X <> 0)) (PreH17 : (retval_2 = 0)) ,
  TT && emp 
|--
  “ ~((valid_afpoint X Y )) ”
  &&  emp
).

Definition is_on_curve_return_wit_4_split_goal_1 := 
forall (Y: Z) (X: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((Zmod ((Y * Y )) (SM2_P_Z)) <> (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH5 : ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z)) (PreH6 : (0 <= (Zmod ((Y * Y )) (SM2_P_Z)))) (PreH7 : ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z)) (PreH8 : (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)))) (PreH9 : (Y < SM2_P_Z)) (PreH10 : (0 <= Y)) (PreH11 : (X < SM2_P_Z)) (PreH12 : (0 <= X)) (PreH13 : (0 <= retval_2)) (PreH14 : (retval_2 <= 1)) (PreH15 : (retval_2 = 0)) (PreH16 : (X <> 0)) (PreH17 : (retval_2 = 0)) ,
  ~((valid_afpoint X Y ))
.

Definition is_on_curve_return_wit_5 := 
(
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval <> 0)) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (valid_afpoint X Y ) ”
  &&  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
) \/
(
forall (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval <> 0)) ,
  TT && emp 
|--
  “ (valid_afpoint 0 0 ) ”
  &&  emp
).

Definition is_on_curve_return_wit_5_split_goal_1 := 
forall (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : (X = 0)) (PreH5 : (Y = 0)) (PreH6 : (retval <> 0)) ,
  (valid_afpoint 0 0 )
.

Definition is_on_curve_partial_solve_wit_1 := 
forall (point_pre: Z) (Y: Z) (X: Z) ,
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition is_on_curve_partial_solve_wit_2 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (Y <> 0)) (PreH5 : (retval = 0)) ,
  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (UndefStructPredu32 ( &( "x3" ) ) )
  **  (UndefStructPredu32 ( &( "y2" ) ) )
  **  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (UInt64Array.undef_full &(( &( "y2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (UndefStructPredu32 ( &( "x3" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_3 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : (X <> 0)) (PreH5 : (retval = 0)) ,
  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (UndefStructPredu32 ( &( "x3" ) ) )
  **  (UndefStructPredu32 ( &( "y2" ) ) )
  **  (store_afpoint_fields point_pre X Y )
  **  (store_sm2_a )
  **  (store_sm2_b )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (UInt64Array.undef_full &(( &( "y2" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (UndefStructPredu32 ( &( "x3" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_4 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (UndefStructPredu32 ( &( "x3" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UInt64Array.undef_full &(( &( "x3" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_5 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (UndefStructPredu32 ( &( "x3" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UInt64Array.undef_full &(( &( "x3" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_6_pure := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  “ (( &( "x3" ) ) = ( &( "x3" ) )) ”
.

Definition is_on_curve_partial_solve_wit_6_aux := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  “ (( &( "x3" ) ) = ( &( "x3" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_6 := is_on_curve_partial_solve_wit_6_pure -> is_on_curve_partial_solve_wit_6_aux.

Definition is_on_curve_partial_solve_wit_7_pure := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  “ (( &( "x3" ) ) = ( &( "x3" ) )) ”
.

Definition is_on_curve_partial_solve_wit_7_aux := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
|--
  “ (( &( "x3" ) ) = ( &( "x3" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_a )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_7 := is_on_curve_partial_solve_wit_7_pure -> is_on_curve_partial_solve_wit_7_aux.

Definition is_on_curve_partial_solve_wit_8 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (( &( "x3" ) ) = ( &( "x3" ) ))) (PreH2 : (Y < SM2_P_Z)) (PreH3 : (0 <= Y)) (PreH4 : (X < SM2_P_Z)) (PreH5 : (0 <= X)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (Y <> 0)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_b )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UInt64Array.undef_full &(( &( "ax" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_9 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (( &( "x3" ) ) = ( &( "x3" ) ))) (PreH2 : (Y < SM2_P_Z)) (PreH3 : (0 <= Y)) (PreH4 : (X < SM2_P_Z)) (PreH5 : (0 <= X)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (X <> 0)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (UndefStructPredu32 ( &( "ax" ) ) )
  **  (store_sm2_b )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (UInt64Array.undef_full &(( &( "ax" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_10 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (store_sm2_b )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "res" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_11 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (UndefStructPredu32 ( &( "res" ) ) )
  **  (store_sm2_b )
|--
  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (UInt64Array.undef_full &(( &( "res" ) )->ₛ "v") 4 )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (store_sm2_b )
.

Definition is_on_curve_partial_solve_wit_12_pure := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ (( &( "res" ) ) = ( &( "res" ) )) ”
.

Definition is_on_curve_partial_solve_wit_12_aux := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (Y <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
|--
  “ (( &( "res" ) ) = ( &( "res" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
.

Definition is_on_curve_partial_solve_wit_12 := is_on_curve_partial_solve_wit_12_pure -> is_on_curve_partial_solve_wit_12_aux.

Definition is_on_curve_partial_solve_wit_13_pure := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ (( &( "res" ) ) = ( &( "res" ) )) ”
.

Definition is_on_curve_partial_solve_wit_13_aux := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (Y < SM2_P_Z)) (PreH2 : (0 <= Y)) (PreH3 : (X < SM2_P_Z)) (PreH4 : (0 <= X)) (PreH5 : (0 <= retval)) (PreH6 : (retval <= 1)) (PreH7 : (retval = 0)) (PreH8 : (X <> 0)) (PreH9 : (retval = 0)) ,
  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_sm2_p )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
|--
  “ (( &( "res" ) ) = ( &( "res" ) )) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_fp ( &( "res" ) ) (Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
.

Definition is_on_curve_partial_solve_wit_13 := is_on_curve_partial_solve_wit_13_pure -> is_on_curve_partial_solve_wit_13_aux.

Definition is_on_curve_partial_solve_wit_14 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (( &( "res" ) ) = ( &( "res" ) ))) (PreH2 : (Y < SM2_P_Z)) (PreH3 : (0 <= Y)) (PreH4 : (X < SM2_P_Z)) (PreH5 : (0 <= X)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (Y <> 0)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "res" ) ) (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
|--
  “ ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((Y * Y )) (SM2_P_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z))) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (Y <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (store_u256 ( &( "res" ) ) (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
.

Definition is_on_curve_partial_solve_wit_15 := 
forall (point_pre: Z) (Y: Z) (X: Z) (retval: Z) (PreH1 : (( &( "res" ) ) = ( &( "res" ) ))) (PreH2 : (Y < SM2_P_Z)) (PreH3 : (0 <= Y)) (PreH4 : (X < SM2_P_Z)) (PreH5 : (0 <= X)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (X <> 0)) (PreH10 : (retval = 0)) ,
  (store_fp ( &( "res" ) ) (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
  **  (store_fp ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
|--
  “ ((Zmod ((Y * Y )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod ((Y * Y )) (SM2_P_Z))) ” 
  &&  “ ((Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) < SM2_P_Z) ” 
  &&  “ (0 <= (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z))) ” 
  &&  “ (Y < SM2_P_Z) ” 
  &&  “ (0 <= Y) ” 
  &&  “ (X < SM2_P_Z) ” 
  &&  “ (0 <= X) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X <> 0) ” 
  &&  “ (retval = 0) ”
  &&  (store_u256 ( &( "y2" ) ) (Zmod ((Y * Y )) (SM2_P_Z)) )
  **  (store_u256 ( &( "res" ) ) (Zmod (((Zmod (((Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) + (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )) (SM2_P_Z)) + SM2_B_Z )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_b" ) ) SM2_B_Z )
  **  (store_sm2_p )
  **  (store_fp ( &( "x3" ) ) (Zmod ((X * (Zmod ((X * X )) (SM2_P_Z)) )) (SM2_P_Z)) )
  **  (store_fp ( &( "ax" ) ) (Zmod ((SM2_A_Z * X )) (SM2_P_Z)) )
  **  (store_fp ( &( "SM2_a" ) ) SM2_A_Z )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "x") X )
  **  (store_sm2_rhop )
  **  (store_fp &((point_pre)  # "AFPoint" ->ₛ "y") Y )
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include sm2_constants_Strategy_Correct.
Include ecc_representation_Strategy_Correct.
Include ecc_constants_Strategy_Correct.

Axiom proof_of_is_on_curve_safety_wit_1 : is_on_curve_safety_wit_1.
Axiom proof_of_is_on_curve_safety_wit_2 : is_on_curve_safety_wit_2.
Axiom proof_of_is_on_curve_safety_wit_3 : is_on_curve_safety_wit_3.
Axiom proof_of_is_on_curve_safety_wit_4 : is_on_curve_safety_wit_4.
Axiom proof_of_is_on_curve_entail_wit_1_1 : is_on_curve_entail_wit_1_1.
Axiom proof_of_is_on_curve_entail_wit_1_2 : is_on_curve_entail_wit_1_2.
Axiom proof_of_is_on_curve_entail_wit_1_3 : is_on_curve_entail_wit_1_3.
Axiom proof_of_is_on_curve_entail_wit_2_1 : is_on_curve_entail_wit_2_1.
Axiom proof_of_is_on_curve_entail_wit_2_2 : is_on_curve_entail_wit_2_2.
Axiom proof_of_is_on_curve_entail_wit_2_3 : is_on_curve_entail_wit_2_3.
Axiom proof_of_is_on_curve_entail_wit_3_1 : is_on_curve_entail_wit_3_1.
Axiom proof_of_is_on_curve_entail_wit_3_2 : is_on_curve_entail_wit_3_2.
Axiom proof_of_is_on_curve_entail_wit_4_1 : is_on_curve_entail_wit_4_1.
Axiom proof_of_is_on_curve_entail_wit_4_2 : is_on_curve_entail_wit_4_2.
Axiom proof_of_is_on_curve_return_wit_1 : is_on_curve_return_wit_1.
Axiom proof_of_is_on_curve_return_wit_2 : is_on_curve_return_wit_2.
Axiom proof_of_is_on_curve_return_wit_3 : is_on_curve_return_wit_3.
Axiom proof_of_is_on_curve_return_wit_4 : is_on_curve_return_wit_4.
Axiom proof_of_is_on_curve_return_wit_5 : is_on_curve_return_wit_5.
Axiom proof_of_is_on_curve_partial_solve_wit_1 : is_on_curve_partial_solve_wit_1.
Axiom proof_of_is_on_curve_partial_solve_wit_2 : is_on_curve_partial_solve_wit_2.
Axiom proof_of_is_on_curve_partial_solve_wit_3 : is_on_curve_partial_solve_wit_3.
Axiom proof_of_is_on_curve_partial_solve_wit_4 : is_on_curve_partial_solve_wit_4.
Axiom proof_of_is_on_curve_partial_solve_wit_5 : is_on_curve_partial_solve_wit_5.
Axiom proof_of_is_on_curve_partial_solve_wit_6_pure : is_on_curve_partial_solve_wit_6_pure.
Axiom proof_of_is_on_curve_partial_solve_wit_6 : is_on_curve_partial_solve_wit_6.
Axiom proof_of_is_on_curve_partial_solve_wit_7_pure : is_on_curve_partial_solve_wit_7_pure.
Axiom proof_of_is_on_curve_partial_solve_wit_7 : is_on_curve_partial_solve_wit_7.
Axiom proof_of_is_on_curve_partial_solve_wit_8 : is_on_curve_partial_solve_wit_8.
Axiom proof_of_is_on_curve_partial_solve_wit_9 : is_on_curve_partial_solve_wit_9.
Axiom proof_of_is_on_curve_partial_solve_wit_10 : is_on_curve_partial_solve_wit_10.
Axiom proof_of_is_on_curve_partial_solve_wit_11 : is_on_curve_partial_solve_wit_11.
Axiom proof_of_is_on_curve_partial_solve_wit_12_pure : is_on_curve_partial_solve_wit_12_pure.
Axiom proof_of_is_on_curve_partial_solve_wit_12 : is_on_curve_partial_solve_wit_12.
Axiom proof_of_is_on_curve_partial_solve_wit_13_pure : is_on_curve_partial_solve_wit_13_pure.
Axiom proof_of_is_on_curve_partial_solve_wit_13 : is_on_curve_partial_solve_wit_13.
Axiom proof_of_is_on_curve_partial_solve_wit_14 : is_on_curve_partial_solve_wit_14.
Axiom proof_of_is_on_curve_partial_solve_wit_15 : is_on_curve_partial_solve_wit_15.

End VC_Correct.
