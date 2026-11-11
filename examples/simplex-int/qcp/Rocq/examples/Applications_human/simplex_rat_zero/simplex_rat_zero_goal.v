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
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib.
Local Open Scope sac.

(*----- Function rat_zero -----*)

Definition rat_zero_safety_wit_1_out_known := 
forall (r_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_zero_safety_wit_2_out_undef := 
forall (r_pre: Z) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_zero_safety_wit_3_out_known := 
forall (r_pre: Z) (oldd_out_known: Z) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_zero_safety_wit_4_out_undef := 
forall (r_pre: Z) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_zero_return_wit_1_out_known := 
forall (r_pre: Z) ,
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> 1)
.

Definition rat_zero_return_wit_2_out_undef := 
forall (r_pre: Z) ,
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> 1)
.

Module Type VC_Correct.


Axiom proof_of_rat_zero_safety_wit_1_out_known : rat_zero_safety_wit_1_out_known.
Axiom proof_of_rat_zero_safety_wit_2_out_undef : rat_zero_safety_wit_2_out_undef.
Axiom proof_of_rat_zero_safety_wit_3_out_known : rat_zero_safety_wit_3_out_known.
Axiom proof_of_rat_zero_safety_wit_4_out_undef : rat_zero_safety_wit_4_out_undef.
Axiom proof_of_rat_zero_return_wit_1_out_known : rat_zero_return_wit_1_out_known.
Axiom proof_of_rat_zero_return_wit_2_out_undef : rat_zero_return_wit_2_out_undef.

End VC_Correct.
