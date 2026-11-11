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

(*----- Function montg_add_jpoint_ex -----*)

Definition montg_add_jpoint_ex_return_wit_1_r_eq_a := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (r_pre = a_pre)) (PreH3 : (r_pre = a_pre)) ,
  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_jpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint r_pre (sm2_point_add (P_r_eq_a) (Q_r_eq_a)) )
  **  (store_mont_jpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_ex_return_wit_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) (retval: Z) (PreH1 : (retval = 1)) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint b_pre Q_non_alias )
  **  (store_mont_jpoint r_pre (sm2_point_add (P_non_alias) (Q_non_alias)) )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a_pure := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (PreH1 : (r_pre = a_pre)) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_mont_jpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ”
.

Definition montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a_aux := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_r_eq_a: ec_point) (P_r_eq_a: ec_point) (PreH1 : (r_pre = a_pre)) ,
  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_mont_jpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  “ (r_pre = a_pre) ” 
  &&  “ (r_pre = a_pre) ”
  &&  (store_mont_jpoint a_pre P_r_eq_a )
  **  (store_mont_jpoint b_pre Q_r_eq_a )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Definition montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a := montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a_pure -> montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a_aux.

Definition montg_add_jpoint_ex_partial_solve_wit_2_non_alias := 
forall (r_pre: Z) (b_pre: Z) (a_pre: Z) (Q_non_alias: ec_point) (P_non_alias: ec_point) ,
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
|--
  (store_mont_jpoint a_pre P_non_alias )
  **  (store_mont_jpoint b_pre Q_non_alias )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "x" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "y" .ₛ "v") 4 )
  **  (UInt64Array.undef_full &((r_pre)  # "JPoint" ->ₛ "z" .ₛ "v") 4 )
  **  (store_bn_zero )
  **  (store_sm2_p )
  **  (store_sm2_rhop )
.

Module Type VC_Correct.


Axiom proof_of_montg_add_jpoint_ex_return_wit_1_r_eq_a : montg_add_jpoint_ex_return_wit_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_ex_return_wit_2_non_alias : montg_add_jpoint_ex_return_wit_2_non_alias.
Axiom proof_of_montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a_pure : montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a_pure.
Axiom proof_of_montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a : montg_add_jpoint_ex_partial_solve_wit_1_r_eq_a.
Axiom proof_of_montg_add_jpoint_ex_partial_solve_wit_2_non_alias : montg_add_jpoint_ex_partial_solve_wit_2_non_alias.

End VC_Correct.
