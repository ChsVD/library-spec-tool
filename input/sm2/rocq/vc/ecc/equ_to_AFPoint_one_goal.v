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
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_goal.
From SimpleC.EE.Applications_human.sm2.strategy Require Import ecc_representation_strategy_proof.

(*----- Function equ_to_AFPoint_one -----*)

Definition equ_to_AFPoint_one_safety_wit_1 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 1)) (PreH4 : (Y_base = 0)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (X_base <> 0)) (PreH10 : (Y_base < SM2_P_Z)) (PreH11 : (0 <= Y_base)) (PreH12 : (X_base < SM2_P_Z)) (PreH13 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ False ”
.

Definition equ_to_AFPoint_one_safety_wit_2 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (0 <= retval_2)) (PreH2 : (retval_2 <= 1)) (PreH3 : (retval_2 = 0)) (PreH4 : (Y_base <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (0 <= retval)) (PreH7 : (retval <= 1)) (PreH8 : (retval = 0)) (PreH9 : (X_base <> 0)) (PreH10 : (Y_base < SM2_P_Z)) (PreH11 : (0 <= Y_base)) (PreH12 : (X_base < SM2_P_Z)) (PreH13 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  ((( &( "point" ) )) # Ptr  |-> point_pre)
|--
  “ False ”
.

Definition equ_to_AFPoint_one_return_wit_1 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (Y_base = 0)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (X_base = 0)) (PreH11 : (Y_base < SM2_P_Z)) (PreH12 : (0 <= Y_base)) (PreH13 : (X_base < SM2_P_Z)) (PreH14 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ (X_base = 0) ” 
  &&  “ (Y_base = 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Y_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (X_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
.

Definition equ_to_AFPoint_one_return_wit_2 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 1)) (PreH5 : (Y_base = 0)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (X_base = 0)) (PreH11 : (Y_base < SM2_P_Z)) (PreH12 : (0 <= Y_base)) (PreH13 : (X_base < SM2_P_Z)) (PreH14 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
|--
  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (X_base = 0) ” 
  &&  “ (Y_base = 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base )
.

Definition equ_to_AFPoint_one_return_wit_3 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (Y_base <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (X_base = 0)) (PreH11 : (Y_base < SM2_P_Z)) (PreH12 : (0 <= Y_base)) (PreH13 : (X_base < SM2_P_Z)) (PreH14 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Y_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base )
.

Definition equ_to_AFPoint_one_return_wit_4 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 1)) (PreH4 : (retval_2 = 0)) (PreH5 : (Y_base <> 0)) (PreH6 : (retval <> 0)) (PreH7 : (0 <= retval)) (PreH8 : (retval <= 1)) (PreH9 : (retval = 1)) (PreH10 : (X_base = 0)) (PreH11 : (Y_base < SM2_P_Z)) (PreH12 : (0 <= Y_base)) (PreH13 : (X_base < SM2_P_Z)) (PreH14 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
|--
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ (X_base = 0) ” 
  &&  “ (Y_base = 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ (Y_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ (X_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
.

Definition equ_to_AFPoint_one_return_wit_5 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (X_base = 0)) (PreH6 : (Y_base < SM2_P_Z)) (PreH7 : (0 <= Y_base)) (PreH8 : (X_base < SM2_P_Z)) (PreH9 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ (X_base = 0) ” 
  &&  “ (Y_base = 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Y_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (X_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
.

Definition equ_to_AFPoint_one_return_wit_6 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (X_base <> 0)) (PreH6 : (Y_base < SM2_P_Z)) (PreH7 : (0 <= Y_base)) (PreH8 : (X_base < SM2_P_Z)) (PreH9 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (Y_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ (X_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
.

Definition equ_to_AFPoint_one_partial_solve_wit_1 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) ,
  (store_afpoint_fields point_pre X_base Y_base )
|--
  “ (Y_base < SM2_P_Z) ” 
  &&  “ (0 <= Y_base) ” 
  &&  “ (X_base < SM2_P_Z) ” 
  &&  “ (0 <= X_base) ”
  &&  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
.

Definition equ_to_AFPoint_one_partial_solve_wit_2 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : (X_base <> 0)) (PreH6 : (Y_base < SM2_P_Z)) (PreH7 : (0 <= Y_base)) (PreH8 : (X_base < SM2_P_Z)) (PreH9 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (X_base <> 0) ” 
  &&  “ (Y_base < SM2_P_Z) ” 
  &&  “ (0 <= Y_base) ” 
  &&  “ (X_base < SM2_P_Z) ” 
  &&  “ (0 <= X_base) ”
  &&  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
.

Definition equ_to_AFPoint_one_partial_solve_wit_3 := 
forall (point_pre: Z) (Y_base: Z) (X_base: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : (X_base = 0)) (PreH6 : (Y_base < SM2_P_Z)) (PreH7 : (0 <= Y_base)) (PreH8 : (X_base < SM2_P_Z)) (PreH9 : (0 <= X_base)) ,
  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (X_base = 0) ” 
  &&  “ (Y_base < SM2_P_Z) ” 
  &&  “ (0 <= Y_base) ” 
  &&  “ (X_base < SM2_P_Z) ” 
  &&  “ (0 <= X_base) ”
  &&  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "y") Y_base )
  **  (store_u256 &((point_pre)  # "AFPoint" ->ₛ "x") X_base )
.

Definition equ_to_AFPoint_one_derive_point_by_base := 
forall (point_pre: Z) (P_point: ec_point) ,
  (store_afpoint point_pre P_point )
|--
EX (X_base: Z) (Y_base: Z) ,
  ((store_afpoint_fields point_pre X_base Y_base ))
  **
  (((EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (X_base = 0) ” 
  &&  “ (Y_base = 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (Y_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base ))
  ||
  (EX retval_2,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 1) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (X_base <> 0) ”
  &&  (store_afpoint_fields point_pre X_base Y_base )))
  -*
  ((EX retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (P_point = ECInfinity) ”
  &&  (store_afpoint point_pre P_point ))
  ||
  (EX retval,
  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ (P_point <> ECInfinity) ”
  &&  (store_afpoint point_pre P_point ))))
.

Module Type VC_Correct.

Include sm2_representation_Strategy_Correct.
Include ecc_representation_Strategy_Correct.

Axiom proof_of_equ_to_AFPoint_one_safety_wit_1 : equ_to_AFPoint_one_safety_wit_1.
Axiom proof_of_equ_to_AFPoint_one_safety_wit_2 : equ_to_AFPoint_one_safety_wit_2.
Axiom proof_of_equ_to_AFPoint_one_return_wit_1 : equ_to_AFPoint_one_return_wit_1.
Axiom proof_of_equ_to_AFPoint_one_return_wit_2 : equ_to_AFPoint_one_return_wit_2.
Axiom proof_of_equ_to_AFPoint_one_return_wit_3 : equ_to_AFPoint_one_return_wit_3.
Axiom proof_of_equ_to_AFPoint_one_return_wit_4 : equ_to_AFPoint_one_return_wit_4.
Axiom proof_of_equ_to_AFPoint_one_return_wit_5 : equ_to_AFPoint_one_return_wit_5.
Axiom proof_of_equ_to_AFPoint_one_return_wit_6 : equ_to_AFPoint_one_return_wit_6.
Axiom proof_of_equ_to_AFPoint_one_partial_solve_wit_1 : equ_to_AFPoint_one_partial_solve_wit_1.
Axiom proof_of_equ_to_AFPoint_one_partial_solve_wit_2 : equ_to_AFPoint_one_partial_solve_wit_2.
Axiom proof_of_equ_to_AFPoint_one_partial_solve_wit_3 : equ_to_AFPoint_one_partial_solve_wit_3.
Axiom proof_of_equ_to_AFPoint_one_derive_point_by_base : equ_to_AFPoint_one_derive_point_by_base.

End VC_Correct.
