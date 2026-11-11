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
Require Import SimpleC.EE.Applications_human.simplex_checked_mul.simplex_checked_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_div.simplex_rat_div_lib.
Local Open Scope sac.

(*----- Function rat_div -----*)

Definition rat_div_safety_wit_1_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (out_pre = x_pre)) (PreH2 : ((-INT_MAX) <= A_r_eq_x)) (PreH3 : (A_r_eq_x <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_r_eq_x)) (PreH5 : (C_r_eq_x <= INT_MAX)) (PreH6 : (1 <= B_r_eq_x)) (PreH7 : (B_r_eq_x <= INT_MAX)) (PreH8 : (1 <= E_r_eq_x)) (PreH9 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_2_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-INT_MAX) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((-INT_MAX) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= E_out_undef)) (PreH8 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_3_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-INT_MAX) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((-INT_MAX) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= E_out_known)) (PreH8 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_4_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (C_r_eq_x = 0)) (PreH2 : (out_pre = x_pre)) (PreH3 : ((-INT_MAX) <= A_r_eq_x)) (PreH4 : (A_r_eq_x <= INT_MAX)) (PreH5 : ((-INT_MAX) <= C_r_eq_x)) (PreH6 : (C_r_eq_x <= INT_MAX)) (PreH7 : (1 <= B_r_eq_x)) (PreH8 : (B_r_eq_x <= INT_MAX)) (PreH9 : (1 <= E_r_eq_x)) (PreH10 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_5_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (C_out_undef = 0)) (PreH2 : ((-INT_MAX) <= A_out_undef)) (PreH3 : (A_out_undef <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_undef)) (PreH5 : (C_out_undef <= INT_MAX)) (PreH6 : (1 <= B_out_undef)) (PreH7 : (B_out_undef <= INT_MAX)) (PreH8 : (1 <= E_out_undef)) (PreH9 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_6_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (C_out_known = 0)) (PreH2 : ((-INT_MAX) <= A_out_known)) (PreH3 : (A_out_known <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_known)) (PreH5 : (C_out_known <= INT_MAX)) (PreH6 : (1 <= B_out_known)) (PreH7 : (B_out_known <= INT_MAX)) (PreH8 : (1 <= E_out_known)) (PreH9 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_7_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ False ”
.

Definition rat_div_safety_wit_8_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 1)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ False ”
.

Definition rat_div_safety_wit_9_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_div_safety_wit_10_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_div_safety_wit_11_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_div_safety_wit_12_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 1)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_div_safety_wit_13_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_14_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_15_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_16_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ False ”
.

Definition rat_div_safety_wit_17_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ False ”
.

Definition rat_div_safety_wit_18_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_div_safety_wit_19_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_div_safety_wit_20_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_div_safety_wit_21_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_div_safety_wit_22_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_23_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_24_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_25_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_26_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_27_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_div_safety_wit_28_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((A_r_eq_x * E_r_eq_x ) <> (INT_MIN)) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((A_r_eq_x * E_r_eq_x ) <> (INT_MIN)) ”
).

Definition rat_div_safety_wit_28_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((A_r_eq_x * E_r_eq_x ) <> (INT_MIN)) ”
.

Definition rat_div_safety_wit_29_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((A_out_undef * E_out_undef ) <> (INT_MIN)) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((A_out_undef * E_out_undef ) <> (INT_MIN)) ”
).

Definition rat_div_safety_wit_29_out_undef_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((A_out_undef * E_out_undef ) <> (INT_MIN)) ”
.

Definition rat_div_safety_wit_30_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((A_out_known * E_out_known ) <> (INT_MIN)) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((A_out_known * E_out_known ) <> (INT_MIN)) ”
).

Definition rat_div_safety_wit_30_out_known_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((A_out_known * E_out_known ) <> (INT_MIN)) ”
.

Definition rat_div_safety_wit_31_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) <> (INT_MIN)) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) <> (INT_MIN)) ”
).

Definition rat_div_safety_wit_31_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) <> (INT_MIN)) ”
.

Definition rat_div_safety_wit_32_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((B_out_undef * C_out_undef ) <> (INT_MIN)) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((B_out_undef * C_out_undef ) <> (INT_MIN)) ”
).

Definition rat_div_safety_wit_32_out_undef_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((B_out_undef * C_out_undef ) <> (INT_MIN)) ”
.

Definition rat_div_safety_wit_33_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((B_out_known * C_out_known ) <> (INT_MIN)) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((B_out_known * C_out_known ) <> (INT_MIN)) ”
).

Definition rat_div_safety_wit_33_out_known_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((B_out_known * C_out_known ) <> (INT_MIN)) ”
.

Definition rat_div_safety_wit_34_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q ) = (P * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_35_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q ) = (P * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (-(A_r_eq_x * E_r_eq_x )))) (PreH11 : (Q = (-(B_r_eq_x * C_r_eq_x )))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_36_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q ) = (P * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_37_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q ) = (P * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : (P = (-(A_r_eq_x * E_r_eq_x )))) (PreH10 : (Q = (-(B_r_eq_x * C_r_eq_x )))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_38_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q ) = (P * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_39_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q ) = (P * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (-(A_out_undef * E_out_undef )))) (PreH11 : (Q = (-(B_out_undef * C_out_undef )))) (PreH12 : ((B_out_undef * C_out_undef ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_40_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q ) = (P * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_41_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q ) = (P * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : (P = (-(A_out_undef * E_out_undef )))) (PreH10 : (Q = (-(B_out_undef * C_out_undef )))) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_42_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q ) = (P * (-(B_out_known * C_out_known )) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_43_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q ) = (P * (-(B_out_known * C_out_known )) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (-(A_out_known * E_out_known )))) (PreH11 : (Q = (-(B_out_known * C_out_known )))) (PreH12 : ((B_out_known * C_out_known ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_44_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q ) = (P * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_45_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q ) = (P * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : (P = (-(A_out_known * E_out_known )))) (PreH10 : (Q = (-(B_out_known * C_out_known )))) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_46_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_47_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (A_r_eq_x * E_r_eq_x ))) (PreH11 : (Q = (B_r_eq_x * C_r_eq_x ))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_48_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_49_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : (P = (A_r_eq_x * E_r_eq_x ))) (PreH10 : (Q = (B_r_eq_x * C_r_eq_x ))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_50_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_51_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (A_out_undef * E_out_undef ))) (PreH11 : (Q = (B_out_undef * C_out_undef ))) (PreH12 : ((B_out_undef * C_out_undef ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_52_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_53_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : (P = (A_out_undef * E_out_undef ))) (PreH10 : (Q = (B_out_undef * C_out_undef ))) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_54_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_55_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (A_out_known * E_out_known ))) (PreH11 : (Q = (B_out_known * C_out_known ))) (PreH12 : ((B_out_known * C_out_known ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_56_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_safety_wit_57_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : (P = (A_out_known * E_out_known ))) (PreH10 : (Q = (B_out_known * C_out_known ))) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_div_return_wit_1_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_1_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_1_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 )
.

Definition rat_div_return_wit_1_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_2_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH11 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH11 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_2_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH11 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_2_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH11 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 )
.

Definition rat_div_return_wit_2_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH11 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_3_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (A_r_eq_x <> 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_3_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))
.

Definition rat_div_return_wit_3_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2 )
.

Definition rat_div_return_wit_3_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_r_eq_x * E_r_eq_x ))))) ((-(B_r_eq_x * C_r_eq_x )))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_4_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH10 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (A_r_eq_x <> 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH10 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (((A_r_eq_x * E_r_eq_x ) * (-(B_r_eq_x * C_r_eq_x )) ) = ((-(A_r_eq_x * E_r_eq_x )) * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_4_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH10 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (((A_r_eq_x * E_r_eq_x ) * (-(B_r_eq_x * C_r_eq_x )) ) = ((-(A_r_eq_x * E_r_eq_x )) * (B_r_eq_x * C_r_eq_x ) ))
.

Definition rat_div_return_wit_4_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH10 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) )
.

Definition rat_div_return_wit_4_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_r_eq_x * E_r_eq_x )) (-(B_r_eq_x * C_r_eq_x )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_r_eq_x * E_r_eq_x )) * Q_2 ) = (P_2 * (-(B_r_eq_x * C_r_eq_x )) ))) (PreH8 : ((-(A_r_eq_x * E_r_eq_x )) <> 0)) (PreH9 : (P_2 = (-(A_r_eq_x * E_r_eq_x )))) (PreH10 : (Q_2 = (-(B_r_eq_x * C_r_eq_x )))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_5_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_5_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_5_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 )
.

Definition rat_div_return_wit_5_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_6_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH11 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH12 : ((B_out_undef * C_out_undef ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH11 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH12 : ((B_out_undef * C_out_undef ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_6_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH11 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH12 : ((B_out_undef * C_out_undef ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_6_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH11 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH12 : ((B_out_undef * C_out_undef ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 )
.

Definition rat_div_return_wit_6_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH11 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH12 : ((B_out_undef * C_out_undef ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_7_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (A_out_undef <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_7_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))
.

Definition rat_div_return_wit_7_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2 )
.

Definition rat_div_return_wit_7_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_undef * E_out_undef ))))) ((-(B_out_undef * C_out_undef )))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_8_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH10 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (A_out_undef <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH10 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (((A_out_undef * E_out_undef ) * (-(B_out_undef * C_out_undef )) ) = ((-(A_out_undef * E_out_undef )) * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_8_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH10 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (((A_out_undef * E_out_undef ) * (-(B_out_undef * C_out_undef )) ) = ((-(A_out_undef * E_out_undef )) * (B_out_undef * C_out_undef ) ))
.

Definition rat_div_return_wit_8_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH10 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) )
.

Definition rat_div_return_wit_8_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_undef * E_out_undef )) (-(B_out_undef * C_out_undef )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_undef * E_out_undef )) * Q_2 ) = (P_2 * (-(B_out_undef * C_out_undef )) ))) (PreH8 : ((-(A_out_undef * E_out_undef )) <> 0)) (PreH9 : (P_2 = (-(A_out_undef * E_out_undef )))) (PreH10 : (Q_2 = (-(B_out_undef * C_out_undef )))) (PreH11 : ((B_out_undef * C_out_undef ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_9_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_9_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_9_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 )
.

Definition rat_div_return_wit_9_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_10_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_known * E_out_known )))) (PreH11 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH12 : ((B_out_known * C_out_known ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_known * E_out_known )))) (PreH11 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH12 : ((B_out_known * C_out_known ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_10_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_known * E_out_known )))) (PreH11 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH12 : ((B_out_known * C_out_known ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_10_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_known * E_out_known )))) (PreH11 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH12 : ((B_out_known * C_out_known ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 )
.

Definition rat_div_return_wit_10_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (-(A_out_known * E_out_known )))) (PreH11 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH12 : ((B_out_known * C_out_known ) < 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_11_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (A_out_known <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) )) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_11_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))
.

Definition rat_div_return_wit_11_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2 )
.

Definition rat_div_return_wit_11_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : ((Zgcd ((Zabs ((-(A_out_known * E_out_known ))))) ((-(B_out_known * C_out_known )))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) < 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_12_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : (P_2 = (-(A_out_known * E_out_known )))) (PreH10 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (A_out_known <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : (P_2 = (-(A_out_known * E_out_known )))) (PreH10 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (((A_out_known * E_out_known ) * (-(B_out_known * C_out_known )) ) = ((-(A_out_known * E_out_known )) * (B_out_known * C_out_known ) )) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_12_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : (P_2 = (-(A_out_known * E_out_known )))) (PreH10 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (((A_out_known * E_out_known ) * (-(B_out_known * C_out_known )) ) = ((-(A_out_known * E_out_known )) * (B_out_known * C_out_known ) ))
.

Definition rat_div_return_wit_12_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : (P_2 = (-(A_out_known * E_out_known )))) (PreH10 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) )
.

Definition rat_div_return_wit_12_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (-(A_out_known * E_out_known )) (-(B_out_known * C_out_known )) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((-(A_out_known * E_out_known )) * Q_2 ) = (P_2 * (-(B_out_known * C_out_known )) ))) (PreH8 : ((-(A_out_known * E_out_known )) <> 0)) (PreH9 : (P_2 = (-(A_out_known * E_out_known )))) (PreH10 : (Q_2 = (-(B_out_known * C_out_known )))) (PreH11 : ((B_out_known * C_out_known ) < 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_13_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_13_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_13_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 )
.

Definition rat_div_return_wit_13_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_14_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH11 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH11 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_14_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH11 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_14_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH11 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 )
.

Definition rat_div_return_wit_14_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH11 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH12 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH18 : (retval = 1)) (PreH19 : (C_r_eq_x <> 0)) (PreH20 : (out_pre = x_pre)) (PreH21 : ((-INT_MAX) <= A_r_eq_x)) (PreH22 : (A_r_eq_x <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_r_eq_x)) (PreH24 : (C_r_eq_x <= INT_MAX)) (PreH25 : (1 <= B_r_eq_x)) (PreH26 : (B_r_eq_x <= INT_MAX)) (PreH27 : (1 <= E_r_eq_x)) (PreH28 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_15_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (A_r_eq_x <> 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_15_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2 )
.

Definition rat_div_return_wit_15_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_r_eq_x * E_r_eq_x )))) ((B_r_eq_x * C_r_eq_x ))) <> 1)) (PreH10 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH16 : (retval = 1)) (PreH17 : (C_r_eq_x <> 0)) (PreH18 : (out_pre = x_pre)) (PreH19 : ((-INT_MAX) <= A_r_eq_x)) (PreH20 : (A_r_eq_x <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_r_eq_x)) (PreH22 : (C_r_eq_x <= INT_MAX)) (PreH23 : (1 <= B_r_eq_x)) (PreH24 : (B_r_eq_x <= INT_MAX)) (PreH25 : (1 <= E_r_eq_x)) (PreH26 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_16_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH10 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) * Q ) = (P * (B_r_eq_x * C_r_eq_x ) )) ” 
  &&  “ (A_r_eq_x <> 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH10 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_16_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH10 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_div_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) )
.

Definition rat_div_return_wit_16_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_r_eq_x * E_r_eq_x ) (B_r_eq_x * C_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_r_eq_x * E_r_eq_x ) * Q_2 ) = (P_2 * (B_r_eq_x * C_r_eq_x ) ))) (PreH8 : ((A_r_eq_x * E_r_eq_x ) <> 0)) (PreH9 : (P_2 = (A_r_eq_x * E_r_eq_x ))) (PreH10 : (Q_2 = (B_r_eq_x * C_r_eq_x ))) (PreH11 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH17 : (retval = 1)) (PreH18 : (C_r_eq_x <> 0)) (PreH19 : (out_pre = x_pre)) (PreH20 : ((-INT_MAX) <= A_r_eq_x)) (PreH21 : (A_r_eq_x <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_r_eq_x)) (PreH23 : (C_r_eq_x <= INT_MAX)) (PreH24 : (1 <= B_r_eq_x)) (PreH25 : (B_r_eq_x <= INT_MAX)) (PreH26 : (1 <= E_r_eq_x)) (PreH27 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_17_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_17_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_17_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 )
.

Definition rat_div_return_wit_17_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_18_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * E_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH12 : ((B_out_undef * C_out_undef ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * E_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH12 : ((B_out_undef * C_out_undef ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_18_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * E_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH12 : ((B_out_undef * C_out_undef ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_18_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * E_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH12 : ((B_out_undef * C_out_undef ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 )
.

Definition rat_div_return_wit_18_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * E_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH12 : ((B_out_undef * C_out_undef ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_undef <> 0)) (PreH20 : ((-INT_MAX) <= A_out_undef)) (PreH21 : (A_out_undef <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_undef)) (PreH23 : (C_out_undef <= INT_MAX)) (PreH24 : (1 <= B_out_undef)) (PreH25 : (B_out_undef <= INT_MAX)) (PreH26 : (1 <= E_out_undef)) (PreH27 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_19_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (A_out_undef <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_19_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2 )
.

Definition rat_div_return_wit_19_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * E_out_undef )))) ((B_out_undef * C_out_undef ))) <> 1)) (PreH10 : ((B_out_undef * C_out_undef ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_undef <> 0)) (PreH18 : ((-INT_MAX) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= E_out_undef)) (PreH25 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_20_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * E_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * E_out_undef ) * Q ) = (P * (B_out_undef * C_out_undef ) )) ” 
  &&  “ (A_out_undef <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * E_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_20_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * E_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_div_result A_out_undef B_out_undef C_out_undef E_out_undef (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) )
.

Definition rat_div_return_wit_20_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * E_out_undef ) (B_out_undef * C_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * E_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * C_out_undef ) ))) (PreH8 : ((A_out_undef * E_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * E_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * C_out_undef ))) (PreH11 : ((B_out_undef * C_out_undef ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_undef <> 0)) (PreH19 : ((-INT_MAX) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= E_out_undef)) (PreH26 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_21_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_21_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_21_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 )
.

Definition rat_div_return_wit_21_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_22_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * E_out_known ))) (PreH11 : (Q_2 = (B_out_known * C_out_known ))) (PreH12 : ((B_out_known * C_out_known ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * E_out_known ))) (PreH11 : (Q_2 = (B_out_known * C_out_known ))) (PreH12 : ((B_out_known * C_out_known ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_22_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * E_out_known ))) (PreH11 : (Q_2 = (B_out_known * C_out_known ))) (PreH12 : ((B_out_known * C_out_known ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_div_return_wit_22_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * E_out_known ))) (PreH11 : (Q_2 = (B_out_known * C_out_known ))) (PreH12 : ((B_out_known * C_out_known ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known 0 1 )
.

Definition rat_div_return_wit_22_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * E_out_known ))) (PreH11 : (Q_2 = (B_out_known * C_out_known ))) (PreH12 : ((B_out_known * C_out_known ) >= 0)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH18 : (retval = 1)) (PreH19 : (C_out_known <> 0)) (PreH20 : ((-INT_MAX) <= A_out_known)) (PreH21 : (A_out_known <= INT_MAX)) (PreH22 : ((-INT_MAX) <= C_out_known)) (PreH23 : (C_out_known <= INT_MAX)) (PreH24 : (1 <= B_out_known)) (PreH25 : (B_out_known <= INT_MAX)) (PreH26 : (1 <= E_out_known)) (PreH27 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_23_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (A_out_known <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_23_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2 )
.

Definition rat_div_return_wit_23_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * E_out_known )))) ((B_out_known * C_out_known ))) <> 1)) (PreH10 : ((B_out_known * C_out_known ) >= 0)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH16 : (retval = 1)) (PreH17 : (C_out_known <> 0)) (PreH18 : ((-INT_MAX) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= E_out_known)) (PreH25 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_24_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * E_out_known ))) (PreH10 : (Q_2 = (B_out_known * C_out_known ))) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * E_out_known ) * Q ) = (P * (B_out_known * C_out_known ) )) ” 
  &&  “ (A_out_known <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * E_out_known ))) (PreH10 : (Q_2 = (B_out_known * C_out_known ))) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known (A_out_known * E_out_known ) (B_out_known * C_out_known ) ) ” 
  &&  “ (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_24_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * E_out_known ))) (PreH10 : (Q_2 = (B_out_known * C_out_known ))) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_div_result A_out_known B_out_known C_out_known E_out_known (A_out_known * E_out_known ) (B_out_known * C_out_known ) )
.

Definition rat_div_return_wit_24_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * E_out_known ) (B_out_known * C_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * E_out_known ) * Q_2 ) = (P_2 * (B_out_known * C_out_known ) ))) (PreH8 : ((A_out_known * E_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * E_out_known ))) (PreH10 : (Q_2 = (B_out_known * C_out_known ))) (PreH11 : ((B_out_known * C_out_known ) >= 0)) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH17 : (retval = 1)) (PreH18 : (C_out_known <> 0)) (PreH19 : ((-INT_MAX) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((-INT_MAX) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= E_out_known)) (PreH26 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_25_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_25_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (C_r_eq_x <> 0)) (PreH8 : (out_pre = x_pre)) (PreH9 : ((-INT_MAX) <= A_r_eq_x)) (PreH10 : (A_r_eq_x <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_r_eq_x)) (PreH12 : (C_r_eq_x <= INT_MAX)) (PreH13 : (1 <= B_r_eq_x)) (PreH14 : (B_r_eq_x <= INT_MAX)) (PreH15 : (1 <= E_r_eq_x)) (PreH16 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_26_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_26_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_undef <> 0)) (PreH8 : ((-INT_MAX) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= E_out_undef)) (PreH15 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_27_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_27_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : (C_out_known <> 0)) (PreH8 : ((-INT_MAX) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= E_out_known)) (PreH15 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_28_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_28_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_div_return_wit_29_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_29_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_div_return_wit_30_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_30_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_div_return_wit_31_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (C_r_eq_x = 0)) (PreH2 : (out_pre = x_pre)) (PreH3 : ((-INT_MAX) <= A_r_eq_x)) (PreH4 : (A_r_eq_x <= INT_MAX)) (PreH5 : ((-INT_MAX) <= C_r_eq_x)) (PreH6 : (C_r_eq_x <= INT_MAX)) (PreH7 : (1 <= B_r_eq_x)) (PreH8 : (B_r_eq_x <= INT_MAX)) (PreH9 : (1 <= E_r_eq_x)) (PreH10 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (C_r_eq_x = 0)) (PreH2 : (out_pre = x_pre)) (PreH3 : ((-INT_MAX) <= A_r_eq_x)) (PreH4 : (A_r_eq_x <= INT_MAX)) (PreH5 : ((-INT_MAX) <= C_r_eq_x)) (PreH6 : (C_r_eq_x <= INT_MAX)) (PreH7 : (1 <= B_r_eq_x)) (PreH8 : (B_r_eq_x <= INT_MAX)) (PreH9 : (1 <= E_r_eq_x)) (PreH10 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (0) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_div_return_wit_31_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (C_r_eq_x = 0)) (PreH2 : (out_pre = x_pre)) (PreH3 : ((-INT_MAX) <= A_r_eq_x)) (PreH4 : (A_r_eq_x <= INT_MAX)) (PreH5 : ((-INT_MAX) <= C_r_eq_x)) (PreH6 : (C_r_eq_x <= INT_MAX)) (PreH7 : (1 <= B_r_eq_x)) (PreH8 : (B_r_eq_x <= INT_MAX)) (PreH9 : (1 <= E_r_eq_x)) (PreH10 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_r_eq_x) (B_r_eq_x) (0) (E_r_eq_x)))
.

Definition rat_div_return_wit_32_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (C_out_undef = 0)) (PreH2 : ((-INT_MAX) <= A_out_undef)) (PreH3 : (A_out_undef <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_undef)) (PreH5 : (C_out_undef <= INT_MAX)) (PreH6 : (1 <= B_out_undef)) (PreH7 : (B_out_undef <= INT_MAX)) (PreH8 : (1 <= E_out_undef)) (PreH9 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (C_out_undef = 0)) (PreH2 : ((-INT_MAX) <= A_out_undef)) (PreH3 : (A_out_undef <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_undef)) (PreH5 : (C_out_undef <= INT_MAX)) (PreH6 : (1 <= B_out_undef)) (PreH7 : (B_out_undef <= INT_MAX)) (PreH8 : (1 <= E_out_undef)) (PreH9 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (0) (E_out_undef))) ”
  &&  emp
).

Definition rat_div_return_wit_32_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (C_out_undef = 0)) (PreH2 : ((-INT_MAX) <= A_out_undef)) (PreH3 : (A_out_undef <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_undef)) (PreH5 : (C_out_undef <= INT_MAX)) (PreH6 : (1 <= B_out_undef)) (PreH7 : (B_out_undef <= INT_MAX)) (PreH8 : (1 <= E_out_undef)) (PreH9 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_out_undef) (B_out_undef) (0) (E_out_undef)))
.

Definition rat_div_return_wit_33_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (C_out_known = 0)) (PreH2 : ((-INT_MAX) <= A_out_known)) (PreH3 : (A_out_known <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_known)) (PreH5 : (C_out_known <= INT_MAX)) (PreH6 : (1 <= B_out_known)) (PreH7 : (B_out_known <= INT_MAX)) (PreH8 : (1 <= E_out_known)) (PreH9 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (C_out_known = 0)) (PreH2 : ((-INT_MAX) <= A_out_known)) (PreH3 : (A_out_known <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_known)) (PreH5 : (C_out_known <= INT_MAX)) (PreH6 : (1 <= B_out_known)) (PreH7 : (B_out_known <= INT_MAX)) (PreH8 : (1 <= E_out_known)) (PreH9 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (0) (E_out_known))) ”
  &&  emp
).

Definition rat_div_return_wit_33_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (C_out_known = 0)) (PreH2 : ((-INT_MAX) <= A_out_known)) (PreH3 : (A_out_known <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_known)) (PreH5 : (C_out_known <= INT_MAX)) (PreH6 : (1 <= B_out_known)) (PreH7 : (B_out_known <= INT_MAX)) (PreH8 : (1 <= E_out_known)) (PreH9 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_div_flag (A_out_known) (B_out_known) (0) (E_out_known)))
.

Definition rat_div_partial_solve_wit_1_r_eq_x_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (C_r_eq_x <> 0)) (PreH2 : (out_pre = x_pre)) (PreH3 : ((-INT_MAX) <= A_r_eq_x)) (PreH4 : (A_r_eq_x <= INT_MAX)) (PreH5 : ((-INT_MAX) <= C_r_eq_x)) (PreH6 : (C_r_eq_x <= INT_MAX)) (PreH7 : (1 <= B_r_eq_x)) (PreH8 : (B_r_eq_x <= INT_MAX)) (PreH9 : (1 <= E_r_eq_x)) (PreH10 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (A_r_eq_x = A_r_eq_x) ” 
  &&  “ (E_r_eq_x = E_r_eq_x) ” 
  &&  “ ((INT_MIN) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
.

Definition rat_div_partial_solve_wit_1_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (C_r_eq_x <> 0)) (PreH2 : (out_pre = x_pre)) (PreH3 : ((-INT_MAX) <= A_r_eq_x)) (PreH4 : (A_r_eq_x <= INT_MAX)) (PreH5 : ((-INT_MAX) <= C_r_eq_x)) (PreH6 : (C_r_eq_x <= INT_MAX)) (PreH7 : (1 <= B_r_eq_x)) (PreH8 : (B_r_eq_x <= INT_MAX)) (PreH9 : (1 <= E_r_eq_x)) (PreH10 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (A_r_eq_x = A_r_eq_x) ” 
  &&  “ (E_r_eq_x = E_r_eq_x) ” 
  &&  “ ((INT_MIN) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_1_r_eq_x := rat_div_partial_solve_wit_1_r_eq_x_pure -> rat_div_partial_solve_wit_1_r_eq_x_aux.

Definition rat_div_partial_solve_wit_2_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (C_out_undef <> 0)) (PreH2 : ((-INT_MAX) <= A_out_undef)) (PreH3 : (A_out_undef <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_undef)) (PreH5 : (C_out_undef <= INT_MAX)) (PreH6 : (1 <= B_out_undef)) (PreH7 : (B_out_undef <= INT_MAX)) (PreH8 : (1 <= E_out_undef)) (PreH9 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (A_out_undef = A_out_undef) ” 
  &&  “ (E_out_undef = E_out_undef) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
.

Definition rat_div_partial_solve_wit_2_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : (C_out_undef <> 0)) (PreH2 : ((-INT_MAX) <= A_out_undef)) (PreH3 : (A_out_undef <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_undef)) (PreH5 : (C_out_undef <= INT_MAX)) (PreH6 : (1 <= B_out_undef)) (PreH7 : (B_out_undef <= INT_MAX)) (PreH8 : (1 <= E_out_undef)) (PreH9 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (A_out_undef = A_out_undef) ” 
  &&  “ (E_out_undef = E_out_undef) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ” 
  &&  “ (C_out_undef <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
.

Definition rat_div_partial_solve_wit_2_out_undef := rat_div_partial_solve_wit_2_out_undef_pure -> rat_div_partial_solve_wit_2_out_undef_aux.

Definition rat_div_partial_solve_wit_3_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (C_out_known <> 0)) (PreH2 : ((-INT_MAX) <= A_out_known)) (PreH3 : (A_out_known <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_known)) (PreH5 : (C_out_known <= INT_MAX)) (PreH6 : (1 <= B_out_known)) (PreH7 : (B_out_known <= INT_MAX)) (PreH8 : (1 <= E_out_known)) (PreH9 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (A_out_known = A_out_known) ” 
  &&  “ (E_out_known = E_out_known) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
.

Definition rat_div_partial_solve_wit_3_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : (C_out_known <> 0)) (PreH2 : ((-INT_MAX) <= A_out_known)) (PreH3 : (A_out_known <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_out_known)) (PreH5 : (C_out_known <= INT_MAX)) (PreH6 : (1 <= B_out_known)) (PreH7 : (B_out_known <= INT_MAX)) (PreH8 : (1 <= E_out_known)) (PreH9 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (A_out_known = A_out_known) ” 
  &&  “ (E_out_known = E_out_known) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ” 
  &&  “ (C_out_known <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
.

Definition rat_div_partial_solve_wit_3_out_known := rat_div_partial_solve_wit_3_out_known_pure -> rat_div_partial_solve_wit_3_out_known_aux.

Definition rat_div_partial_solve_wit_4_r_eq_x_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 1)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (B_r_eq_x = B_r_eq_x) ” 
  &&  “ (C_r_eq_x = C_r_eq_x) ” 
  &&  “ ((INT_MIN) <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ”
.

Definition rat_div_partial_solve_wit_4_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 1)) (PreH4 : (C_r_eq_x <> 0)) (PreH5 : (out_pre = x_pre)) (PreH6 : ((-INT_MAX) <= A_r_eq_x)) (PreH7 : (A_r_eq_x <= INT_MAX)) (PreH8 : ((-INT_MAX) <= C_r_eq_x)) (PreH9 : (C_r_eq_x <= INT_MAX)) (PreH10 : (1 <= B_r_eq_x)) (PreH11 : (B_r_eq_x <= INT_MAX)) (PreH12 : (1 <= E_r_eq_x)) (PreH13 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (B_r_eq_x = B_r_eq_x) ” 
  &&  “ (C_r_eq_x = C_r_eq_x) ” 
  &&  “ ((INT_MIN) <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_4_r_eq_x := rat_div_partial_solve_wit_4_r_eq_x_pure -> rat_div_partial_solve_wit_4_r_eq_x_aux.

Definition rat_div_partial_solve_wit_5_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (B_out_undef = B_out_undef) ” 
  &&  “ (C_out_undef = C_out_undef) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ”
.

Definition rat_div_partial_solve_wit_5_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : (C_out_undef <> 0)) (PreH5 : ((-INT_MAX) <= A_out_undef)) (PreH6 : (A_out_undef <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_undef)) (PreH8 : (C_out_undef <= INT_MAX)) (PreH9 : (1 <= B_out_undef)) (PreH10 : (B_out_undef <= INT_MAX)) (PreH11 : (1 <= E_out_undef)) (PreH12 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (B_out_undef = B_out_undef) ” 
  &&  “ (C_out_undef = C_out_undef) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_out_undef <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
.

Definition rat_div_partial_solve_wit_5_out_undef := rat_div_partial_solve_wit_5_out_undef_pure -> rat_div_partial_solve_wit_5_out_undef_aux.

Definition rat_div_partial_solve_wit_6_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 1)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (B_out_known = B_out_known) ” 
  &&  “ (C_out_known = C_out_known) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ”
.

Definition rat_div_partial_solve_wit_6_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 1)) (PreH4 : (C_out_known <> 0)) (PreH5 : ((-INT_MAX) <= A_out_known)) (PreH6 : (A_out_known <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_out_known)) (PreH8 : (C_out_known <= INT_MAX)) (PreH9 : (1 <= B_out_known)) (PreH10 : (B_out_known <= INT_MAX)) (PreH11 : (1 <= E_out_known)) (PreH12 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (B_out_known = B_out_known) ” 
  &&  “ (C_out_known = C_out_known) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_out_known <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
.

Definition rat_div_partial_solve_wit_6_out_known := rat_div_partial_solve_wit_6_out_known_pure -> rat_div_partial_solve_wit_6_out_known_aux.

Definition rat_div_partial_solve_wit_7_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_8_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_9_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_10_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((B_r_eq_x * C_r_eq_x ) >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_11_r_eq_x_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= (-(B_r_eq_x * C_r_eq_x ))) ” 
  &&  “ ((-(B_r_eq_x * C_r_eq_x )) <= INT_MAX) ” 
  &&  “ ((-(A_r_eq_x * E_r_eq_x )) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (-(A_r_eq_x * E_r_eq_x ))) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_r_eq_x <= INT_MAX)) (PreH2 : (C_r_eq_x <= INT_MAX)) (PreH3 : ((-(A_r_eq_x * E_r_eq_x )) <= INT_MAX)) (PreH4 : ((-(B_r_eq_x * C_r_eq_x )) <= INT_MAX)) (PreH5 : (E_r_eq_x >= INT_MIN)) (PreH6 : (C_r_eq_x >= INT_MIN)) (PreH7 : ((-(A_r_eq_x * E_r_eq_x )) >= INT_MIN)) (PreH8 : ((-(B_r_eq_x * C_r_eq_x )) >= INT_MIN)) (PreH9 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH15 : (retval = 1)) (PreH16 : (C_r_eq_x <> 0)) (PreH17 : (out_pre = x_pre)) (PreH18 : ((-INT_MAX) <= A_r_eq_x)) (PreH19 : (A_r_eq_x <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_r_eq_x)) (PreH21 : (C_r_eq_x <= INT_MAX)) (PreH22 : (1 <= B_r_eq_x)) (PreH23 : (B_r_eq_x <= INT_MAX)) (PreH24 : (1 <= E_r_eq_x)) (PreH25 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((-INT_MAX) <= (-(A_r_eq_x * E_r_eq_x ))) ”
).

Definition rat_div_partial_solve_wit_11_r_eq_x_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_r_eq_x <= INT_MAX)) (PreH2 : (C_r_eq_x <= INT_MAX)) (PreH3 : ((-(A_r_eq_x * E_r_eq_x )) <= INT_MAX)) (PreH4 : ((-(B_r_eq_x * C_r_eq_x )) <= INT_MAX)) (PreH5 : (E_r_eq_x >= INT_MIN)) (PreH6 : (C_r_eq_x >= INT_MIN)) (PreH7 : ((-(A_r_eq_x * E_r_eq_x )) >= INT_MIN)) (PreH8 : ((-(B_r_eq_x * C_r_eq_x )) >= INT_MIN)) (PreH9 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH15 : (retval = 1)) (PreH16 : (C_r_eq_x <> 0)) (PreH17 : (out_pre = x_pre)) (PreH18 : ((-INT_MAX) <= A_r_eq_x)) (PreH19 : (A_r_eq_x <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_r_eq_x)) (PreH21 : (C_r_eq_x <= INT_MAX)) (PreH22 : (1 <= B_r_eq_x)) (PreH23 : (B_r_eq_x <= INT_MAX)) (PreH24 : (1 <= E_r_eq_x)) (PreH25 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "d" ) )) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((-INT_MAX) <= (-(A_r_eq_x * E_r_eq_x ))) ”
.

Definition rat_div_partial_solve_wit_11_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= (-(B_r_eq_x * C_r_eq_x ))) ” 
  &&  “ ((-(B_r_eq_x * C_r_eq_x )) <= INT_MAX) ” 
  &&  “ ((-(A_r_eq_x * E_r_eq_x )) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (-(A_r_eq_x * E_r_eq_x ))) ” 
  &&  “ ((B_r_eq_x * C_r_eq_x ) < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_r_eq_x * E_r_eq_x )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_r_eq_x * C_r_eq_x )))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_11_r_eq_x := rat_div_partial_solve_wit_11_r_eq_x_pure -> rat_div_partial_solve_wit_11_r_eq_x_aux.

Definition rat_div_partial_solve_wit_12_out_undef_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_undef * C_out_undef )))
|--
  “ (1 <= (-(B_out_undef * C_out_undef ))) ” 
  &&  “ ((-(B_out_undef * C_out_undef )) <= INT_MAX) ” 
  &&  “ ((-(A_out_undef * E_out_undef )) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (-(A_out_undef * E_out_undef ))) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((-(A_out_undef * E_out_undef )) <= INT_MAX)) (PreH6 : ((-(B_out_undef * C_out_undef )) <= INT_MAX)) (PreH7 : (E_out_undef >= INT_MIN)) (PreH8 : (C_out_undef >= INT_MIN)) (PreH9 : (B_out_undef >= INT_MIN)) (PreH10 : (A_out_undef >= INT_MIN)) (PreH11 : ((-(A_out_undef * E_out_undef )) >= INT_MIN)) (PreH12 : ((-(B_out_undef * C_out_undef )) >= INT_MIN)) (PreH13 : ((B_out_undef * C_out_undef ) < 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_undef <> 0)) (PreH21 : ((-INT_MAX) <= A_out_undef)) (PreH22 : (A_out_undef <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_undef)) (PreH24 : (C_out_undef <= INT_MAX)) (PreH25 : (1 <= B_out_undef)) (PreH26 : (B_out_undef <= INT_MAX)) (PreH27 : (1 <= E_out_undef)) (PreH28 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_undef * C_out_undef )))
|--
  “ ((-INT_MAX) <= (-(A_out_undef * E_out_undef ))) ”
).

Definition rat_div_partial_solve_wit_12_out_undef_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((-(A_out_undef * E_out_undef )) <= INT_MAX)) (PreH6 : ((-(B_out_undef * C_out_undef )) <= INT_MAX)) (PreH7 : (E_out_undef >= INT_MIN)) (PreH8 : (C_out_undef >= INT_MIN)) (PreH9 : (B_out_undef >= INT_MIN)) (PreH10 : (A_out_undef >= INT_MIN)) (PreH11 : ((-(A_out_undef * E_out_undef )) >= INT_MIN)) (PreH12 : ((-(B_out_undef * C_out_undef )) >= INT_MIN)) (PreH13 : ((B_out_undef * C_out_undef ) < 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_undef <> 0)) (PreH21 : ((-INT_MAX) <= A_out_undef)) (PreH22 : (A_out_undef <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_undef)) (PreH24 : (C_out_undef <= INT_MAX)) (PreH25 : (1 <= B_out_undef)) (PreH26 : (B_out_undef <= INT_MAX)) (PreH27 : (1 <= E_out_undef)) (PreH28 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_undef * C_out_undef )))
|--
  “ ((-INT_MAX) <= (-(A_out_undef * E_out_undef ))) ”
.

Definition rat_div_partial_solve_wit_12_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_undef * C_out_undef )))
|--
  “ (1 <= (-(B_out_undef * C_out_undef ))) ” 
  &&  “ ((-(B_out_undef * C_out_undef )) <= INT_MAX) ” 
  &&  “ ((-(A_out_undef * E_out_undef )) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (-(A_out_undef * E_out_undef ))) ” 
  &&  “ ((B_out_undef * C_out_undef ) < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_out_undef <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_undef * E_out_undef )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_undef * C_out_undef )))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
.

Definition rat_div_partial_solve_wit_12_out_undef := rat_div_partial_solve_wit_12_out_undef_pure -> rat_div_partial_solve_wit_12_out_undef_aux.

Definition rat_div_partial_solve_wit_13_out_known_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_known * C_out_known )))
|--
  “ (1 <= (-(B_out_known * C_out_known ))) ” 
  &&  “ ((-(B_out_known * C_out_known )) <= INT_MAX) ” 
  &&  “ ((-(A_out_known * E_out_known )) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (-(A_out_known * E_out_known ))) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((-(A_out_known * E_out_known )) <= INT_MAX)) (PreH6 : ((-(B_out_known * C_out_known )) <= INT_MAX)) (PreH7 : (E_out_known >= INT_MIN)) (PreH8 : (C_out_known >= INT_MIN)) (PreH9 : (B_out_known >= INT_MIN)) (PreH10 : (A_out_known >= INT_MIN)) (PreH11 : ((-(A_out_known * E_out_known )) >= INT_MIN)) (PreH12 : ((-(B_out_known * C_out_known )) >= INT_MIN)) (PreH13 : ((B_out_known * C_out_known ) < 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_known <> 0)) (PreH21 : ((-INT_MAX) <= A_out_known)) (PreH22 : (A_out_known <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_known)) (PreH24 : (C_out_known <= INT_MAX)) (PreH25 : (1 <= B_out_known)) (PreH26 : (B_out_known <= INT_MAX)) (PreH27 : (1 <= E_out_known)) (PreH28 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_known * C_out_known )))
|--
  “ ((-INT_MAX) <= (-(A_out_known * E_out_known ))) ”
).

Definition rat_div_partial_solve_wit_13_out_known_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((-(A_out_known * E_out_known )) <= INT_MAX)) (PreH6 : ((-(B_out_known * C_out_known )) <= INT_MAX)) (PreH7 : (E_out_known >= INT_MIN)) (PreH8 : (C_out_known >= INT_MIN)) (PreH9 : (B_out_known >= INT_MIN)) (PreH10 : (A_out_known >= INT_MIN)) (PreH11 : ((-(A_out_known * E_out_known )) >= INT_MIN)) (PreH12 : ((-(B_out_known * C_out_known )) >= INT_MIN)) (PreH13 : ((B_out_known * C_out_known ) < 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_known <> 0)) (PreH21 : ((-INT_MAX) <= A_out_known)) (PreH22 : (A_out_known <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_known)) (PreH24 : (C_out_known <= INT_MAX)) (PreH25 : (1 <= B_out_known)) (PreH26 : (B_out_known <= INT_MAX)) (PreH27 : (1 <= E_out_known)) (PreH28 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((( &( "n" ) )) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_known * C_out_known )))
|--
  “ ((-INT_MAX) <= (-(A_out_known * E_out_known ))) ”
.

Definition rat_div_partial_solve_wit_13_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) < 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_known * C_out_known )))
|--
  “ (1 <= (-(B_out_known * C_out_known ))) ” 
  &&  “ ((-(B_out_known * C_out_known )) <= INT_MAX) ” 
  &&  “ ((-(A_out_known * E_out_known )) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (-(A_out_known * E_out_known ))) ” 
  &&  “ ((B_out_known * C_out_known ) < 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_out_known) (C_out_known))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_out_known <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (-(A_out_known * E_out_known )))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (-(B_out_known * C_out_known )))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
.

Definition rat_div_partial_solve_wit_13_out_known := rat_div_partial_solve_wit_13_out_known_pure -> rat_div_partial_solve_wit_13_out_known_aux.

Definition rat_div_partial_solve_wit_14_r_eq_x_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= (B_r_eq_x * C_r_eq_x )) ” 
  &&  “ ((B_r_eq_x * C_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((A_r_eq_x * E_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_r_eq_x * E_r_eq_x )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_r_eq_x <= INT_MAX)) (PreH2 : (C_r_eq_x <= INT_MAX)) (PreH3 : ((A_r_eq_x * E_r_eq_x ) <= INT_MAX)) (PreH4 : ((B_r_eq_x * C_r_eq_x ) <= INT_MAX)) (PreH5 : (E_r_eq_x >= INT_MIN)) (PreH6 : (C_r_eq_x >= INT_MIN)) (PreH7 : ((A_r_eq_x * E_r_eq_x ) >= INT_MIN)) (PreH8 : ((B_r_eq_x * C_r_eq_x ) >= INT_MIN)) (PreH9 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH15 : (retval = 1)) (PreH16 : (C_r_eq_x <> 0)) (PreH17 : (out_pre = x_pre)) (PreH18 : ((-INT_MAX) <= A_r_eq_x)) (PreH19 : (A_r_eq_x <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_r_eq_x)) (PreH21 : (C_r_eq_x <= INT_MAX)) (PreH22 : (1 <= B_r_eq_x)) (PreH23 : (B_r_eq_x <= INT_MAX)) (PreH24 : (1 <= E_r_eq_x)) (PreH25 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((-INT_MAX) <= (A_r_eq_x * E_r_eq_x )) ”
).

Definition rat_div_partial_solve_wit_14_r_eq_x_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_r_eq_x <= INT_MAX)) (PreH2 : (C_r_eq_x <= INT_MAX)) (PreH3 : ((A_r_eq_x * E_r_eq_x ) <= INT_MAX)) (PreH4 : ((B_r_eq_x * C_r_eq_x ) <= INT_MAX)) (PreH5 : (E_r_eq_x >= INT_MIN)) (PreH6 : (C_r_eq_x >= INT_MIN)) (PreH7 : ((A_r_eq_x * E_r_eq_x ) >= INT_MIN)) (PreH8 : ((B_r_eq_x * C_r_eq_x ) >= INT_MIN)) (PreH9 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH15 : (retval = 1)) (PreH16 : (C_r_eq_x <> 0)) (PreH17 : (out_pre = x_pre)) (PreH18 : ((-INT_MAX) <= A_r_eq_x)) (PreH19 : (A_r_eq_x <= INT_MAX)) (PreH20 : ((-INT_MAX) <= C_r_eq_x)) (PreH21 : (C_r_eq_x <= INT_MAX)) (PreH22 : (1 <= B_r_eq_x)) (PreH23 : (B_r_eq_x <= INT_MAX)) (PreH24 : (1 <= E_r_eq_x)) (PreH25 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((-INT_MAX) <= (A_r_eq_x * E_r_eq_x )) ”
.

Definition rat_div_partial_solve_wit_14_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_r_eq_x * C_r_eq_x ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH7 : (retval = 1)) (PreH8 : (C_r_eq_x <> 0)) (PreH9 : (out_pre = x_pre)) (PreH10 : ((-INT_MAX) <= A_r_eq_x)) (PreH11 : (A_r_eq_x <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_r_eq_x)) (PreH13 : (C_r_eq_x <= INT_MAX)) (PreH14 : (1 <= B_r_eq_x)) (PreH15 : (B_r_eq_x <= INT_MAX)) (PreH16 : (1 <= E_r_eq_x)) (PreH17 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= (B_r_eq_x * C_r_eq_x )) ” 
  &&  “ ((B_r_eq_x * C_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((A_r_eq_x * E_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_r_eq_x * E_r_eq_x )) ” 
  &&  “ ((B_r_eq_x * C_r_eq_x ) >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_r_eq_x) (C_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_r_eq_x <> 0) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * C_r_eq_x ))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_div_partial_solve_wit_14_r_eq_x := rat_div_partial_solve_wit_14_r_eq_x_pure -> rat_div_partial_solve_wit_14_r_eq_x_aux.

Definition rat_div_partial_solve_wit_15_out_undef_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * C_out_undef ))
|--
  “ (1 <= (B_out_undef * C_out_undef )) ” 
  &&  “ ((B_out_undef * C_out_undef ) <= INT_MAX) ” 
  &&  “ ((A_out_undef * E_out_undef ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_undef * E_out_undef )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((A_out_undef * E_out_undef ) <= INT_MAX)) (PreH6 : ((B_out_undef * C_out_undef ) <= INT_MAX)) (PreH7 : (E_out_undef >= INT_MIN)) (PreH8 : (C_out_undef >= INT_MIN)) (PreH9 : (B_out_undef >= INT_MIN)) (PreH10 : (A_out_undef >= INT_MIN)) (PreH11 : ((A_out_undef * E_out_undef ) >= INT_MIN)) (PreH12 : ((B_out_undef * C_out_undef ) >= INT_MIN)) (PreH13 : ((B_out_undef * C_out_undef ) >= 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_undef <> 0)) (PreH21 : ((-INT_MAX) <= A_out_undef)) (PreH22 : (A_out_undef <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_undef)) (PreH24 : (C_out_undef <= INT_MAX)) (PreH25 : (1 <= B_out_undef)) (PreH26 : (B_out_undef <= INT_MAX)) (PreH27 : (1 <= E_out_undef)) (PreH28 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * C_out_undef ))
|--
  “ ((-INT_MAX) <= (A_out_undef * E_out_undef )) ”
).

Definition rat_div_partial_solve_wit_15_out_undef_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((A_out_undef * E_out_undef ) <= INT_MAX)) (PreH6 : ((B_out_undef * C_out_undef ) <= INT_MAX)) (PreH7 : (E_out_undef >= INT_MIN)) (PreH8 : (C_out_undef >= INT_MIN)) (PreH9 : (B_out_undef >= INT_MIN)) (PreH10 : (A_out_undef >= INT_MIN)) (PreH11 : ((A_out_undef * E_out_undef ) >= INT_MIN)) (PreH12 : ((B_out_undef * C_out_undef ) >= INT_MIN)) (PreH13 : ((B_out_undef * C_out_undef ) >= 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_undef <> 0)) (PreH21 : ((-INT_MAX) <= A_out_undef)) (PreH22 : (A_out_undef <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_undef)) (PreH24 : (C_out_undef <= INT_MAX)) (PreH25 : (1 <= B_out_undef)) (PreH26 : (B_out_undef <= INT_MAX)) (PreH27 : (1 <= E_out_undef)) (PreH28 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * C_out_undef ))
|--
  “ ((-INT_MAX) <= (A_out_undef * E_out_undef )) ”
.

Definition rat_div_partial_solve_wit_15_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_undef * C_out_undef ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_undef <> 0)) (PreH9 : ((-INT_MAX) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= E_out_undef)) (PreH16 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * C_out_undef ))
|--
  “ (1 <= (B_out_undef * C_out_undef )) ” 
  &&  “ ((B_out_undef * C_out_undef ) <= INT_MAX) ” 
  &&  “ ((A_out_undef * E_out_undef ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_undef * E_out_undef )) ” 
  &&  “ ((B_out_undef * C_out_undef ) >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_out_undef) (C_out_undef))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_out_undef <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * C_out_undef ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
.

Definition rat_div_partial_solve_wit_15_out_undef := rat_div_partial_solve_wit_15_out_undef_pure -> rat_div_partial_solve_wit_15_out_undef_aux.

Definition rat_div_partial_solve_wit_16_out_known_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * E_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * C_out_known ))
|--
  “ (1 <= (B_out_known * C_out_known )) ” 
  &&  “ ((B_out_known * C_out_known ) <= INT_MAX) ” 
  &&  “ ((A_out_known * E_out_known ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_known * E_out_known )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((A_out_known * E_out_known ) <= INT_MAX)) (PreH6 : ((B_out_known * C_out_known ) <= INT_MAX)) (PreH7 : (E_out_known >= INT_MIN)) (PreH8 : (C_out_known >= INT_MIN)) (PreH9 : (B_out_known >= INT_MIN)) (PreH10 : (A_out_known >= INT_MIN)) (PreH11 : ((A_out_known * E_out_known ) >= INT_MIN)) (PreH12 : ((B_out_known * C_out_known ) >= INT_MIN)) (PreH13 : ((B_out_known * C_out_known ) >= 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_known <> 0)) (PreH21 : ((-INT_MAX) <= A_out_known)) (PreH22 : (A_out_known <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_known)) (PreH24 : (C_out_known <= INT_MAX)) (PreH25 : (1 <= B_out_known)) (PreH26 : (B_out_known <= INT_MAX)) (PreH27 : (1 <= E_out_known)) (PreH28 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * E_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * C_out_known ))
|--
  “ ((-INT_MAX) <= (A_out_known * E_out_known )) ”
).

Definition rat_div_partial_solve_wit_16_out_known_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (E_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((A_out_known * E_out_known ) <= INT_MAX)) (PreH6 : ((B_out_known * C_out_known ) <= INT_MAX)) (PreH7 : (E_out_known >= INT_MIN)) (PreH8 : (C_out_known >= INT_MIN)) (PreH9 : (B_out_known >= INT_MIN)) (PreH10 : (A_out_known >= INT_MIN)) (PreH11 : ((A_out_known * E_out_known ) >= INT_MIN)) (PreH12 : ((B_out_known * C_out_known ) >= INT_MIN)) (PreH13 : ((B_out_known * C_out_known ) >= 0)) (PreH14 : (retval_2 <> 0)) (PreH15 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH16 : (retval_2 = 1)) (PreH17 : (retval <> 0)) (PreH18 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH19 : (retval = 1)) (PreH20 : (C_out_known <> 0)) (PreH21 : ((-INT_MAX) <= A_out_known)) (PreH22 : (A_out_known <= INT_MAX)) (PreH23 : ((-INT_MAX) <= C_out_known)) (PreH24 : (C_out_known <= INT_MAX)) (PreH25 : (1 <= B_out_known)) (PreH26 : (B_out_known <= INT_MAX)) (PreH27 : (1 <= E_out_known)) (PreH28 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * C_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * E_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * C_out_known ))
|--
  “ ((-INT_MAX) <= (A_out_known * E_out_known )) ”
.

Definition rat_div_partial_solve_wit_16_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((B_out_known * C_out_known ) >= 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (B_out_known) (C_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH7 : (retval = 1)) (PreH8 : (C_out_known <> 0)) (PreH9 : ((-INT_MAX) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((-INT_MAX) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= E_out_known)) (PreH16 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * E_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * C_out_known ))
|--
  “ (1 <= (B_out_known * C_out_known )) ” 
  &&  “ ((B_out_known * C_out_known ) <= INT_MAX) ” 
  &&  “ ((A_out_known * E_out_known ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_known * E_out_known )) ” 
  &&  “ ((B_out_known * C_out_known ) >= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_out_known) (C_out_known))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (C_out_known <> 0) ” 
  &&  “ ((-INT_MAX) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * E_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * C_out_known ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
.

Definition rat_div_partial_solve_wit_16_out_known := rat_div_partial_solve_wit_16_out_known_pure -> rat_div_partial_solve_wit_16_out_known_aux.

Module Type VC_Correct.


Axiom proof_of_rat_div_safety_wit_1_r_eq_x : rat_div_safety_wit_1_r_eq_x.
Axiom proof_of_rat_div_safety_wit_2_out_undef : rat_div_safety_wit_2_out_undef.
Axiom proof_of_rat_div_safety_wit_3_out_known : rat_div_safety_wit_3_out_known.
Axiom proof_of_rat_div_safety_wit_4_r_eq_x : rat_div_safety_wit_4_r_eq_x.
Axiom proof_of_rat_div_safety_wit_5_out_undef : rat_div_safety_wit_5_out_undef.
Axiom proof_of_rat_div_safety_wit_6_out_known : rat_div_safety_wit_6_out_known.
Axiom proof_of_rat_div_safety_wit_7_r_eq_x : rat_div_safety_wit_7_r_eq_x.
Axiom proof_of_rat_div_safety_wit_8_r_eq_x : rat_div_safety_wit_8_r_eq_x.
Axiom proof_of_rat_div_safety_wit_9_out_undef : rat_div_safety_wit_9_out_undef.
Axiom proof_of_rat_div_safety_wit_10_out_undef : rat_div_safety_wit_10_out_undef.
Axiom proof_of_rat_div_safety_wit_11_out_known : rat_div_safety_wit_11_out_known.
Axiom proof_of_rat_div_safety_wit_12_out_known : rat_div_safety_wit_12_out_known.
Axiom proof_of_rat_div_safety_wit_13_r_eq_x : rat_div_safety_wit_13_r_eq_x.
Axiom proof_of_rat_div_safety_wit_14_out_undef : rat_div_safety_wit_14_out_undef.
Axiom proof_of_rat_div_safety_wit_15_out_known : rat_div_safety_wit_15_out_known.
Axiom proof_of_rat_div_safety_wit_16_r_eq_x : rat_div_safety_wit_16_r_eq_x.
Axiom proof_of_rat_div_safety_wit_17_r_eq_x : rat_div_safety_wit_17_r_eq_x.
Axiom proof_of_rat_div_safety_wit_18_out_undef : rat_div_safety_wit_18_out_undef.
Axiom proof_of_rat_div_safety_wit_19_out_undef : rat_div_safety_wit_19_out_undef.
Axiom proof_of_rat_div_safety_wit_20_out_known : rat_div_safety_wit_20_out_known.
Axiom proof_of_rat_div_safety_wit_21_out_known : rat_div_safety_wit_21_out_known.
Axiom proof_of_rat_div_safety_wit_22_r_eq_x : rat_div_safety_wit_22_r_eq_x.
Axiom proof_of_rat_div_safety_wit_23_out_undef : rat_div_safety_wit_23_out_undef.
Axiom proof_of_rat_div_safety_wit_24_out_known : rat_div_safety_wit_24_out_known.
Axiom proof_of_rat_div_safety_wit_25_r_eq_x : rat_div_safety_wit_25_r_eq_x.
Axiom proof_of_rat_div_safety_wit_26_out_undef : rat_div_safety_wit_26_out_undef.
Axiom proof_of_rat_div_safety_wit_27_out_known : rat_div_safety_wit_27_out_known.
Axiom proof_of_rat_div_safety_wit_28_r_eq_x : rat_div_safety_wit_28_r_eq_x.
Axiom proof_of_rat_div_safety_wit_29_out_undef : rat_div_safety_wit_29_out_undef.
Axiom proof_of_rat_div_safety_wit_30_out_known : rat_div_safety_wit_30_out_known.
Axiom proof_of_rat_div_safety_wit_31_r_eq_x : rat_div_safety_wit_31_r_eq_x.
Axiom proof_of_rat_div_safety_wit_32_out_undef : rat_div_safety_wit_32_out_undef.
Axiom proof_of_rat_div_safety_wit_33_out_known : rat_div_safety_wit_33_out_known.
Axiom proof_of_rat_div_safety_wit_34_r_eq_x : rat_div_safety_wit_34_r_eq_x.
Axiom proof_of_rat_div_safety_wit_35_r_eq_x : rat_div_safety_wit_35_r_eq_x.
Axiom proof_of_rat_div_safety_wit_36_r_eq_x : rat_div_safety_wit_36_r_eq_x.
Axiom proof_of_rat_div_safety_wit_37_r_eq_x : rat_div_safety_wit_37_r_eq_x.
Axiom proof_of_rat_div_safety_wit_38_out_undef : rat_div_safety_wit_38_out_undef.
Axiom proof_of_rat_div_safety_wit_39_out_undef : rat_div_safety_wit_39_out_undef.
Axiom proof_of_rat_div_safety_wit_40_out_undef : rat_div_safety_wit_40_out_undef.
Axiom proof_of_rat_div_safety_wit_41_out_undef : rat_div_safety_wit_41_out_undef.
Axiom proof_of_rat_div_safety_wit_42_out_known : rat_div_safety_wit_42_out_known.
Axiom proof_of_rat_div_safety_wit_43_out_known : rat_div_safety_wit_43_out_known.
Axiom proof_of_rat_div_safety_wit_44_out_known : rat_div_safety_wit_44_out_known.
Axiom proof_of_rat_div_safety_wit_45_out_known : rat_div_safety_wit_45_out_known.
Axiom proof_of_rat_div_safety_wit_46_r_eq_x : rat_div_safety_wit_46_r_eq_x.
Axiom proof_of_rat_div_safety_wit_47_r_eq_x : rat_div_safety_wit_47_r_eq_x.
Axiom proof_of_rat_div_safety_wit_48_r_eq_x : rat_div_safety_wit_48_r_eq_x.
Axiom proof_of_rat_div_safety_wit_49_r_eq_x : rat_div_safety_wit_49_r_eq_x.
Axiom proof_of_rat_div_safety_wit_50_out_undef : rat_div_safety_wit_50_out_undef.
Axiom proof_of_rat_div_safety_wit_51_out_undef : rat_div_safety_wit_51_out_undef.
Axiom proof_of_rat_div_safety_wit_52_out_undef : rat_div_safety_wit_52_out_undef.
Axiom proof_of_rat_div_safety_wit_53_out_undef : rat_div_safety_wit_53_out_undef.
Axiom proof_of_rat_div_safety_wit_54_out_known : rat_div_safety_wit_54_out_known.
Axiom proof_of_rat_div_safety_wit_55_out_known : rat_div_safety_wit_55_out_known.
Axiom proof_of_rat_div_safety_wit_56_out_known : rat_div_safety_wit_56_out_known.
Axiom proof_of_rat_div_safety_wit_57_out_known : rat_div_safety_wit_57_out_known.
Axiom proof_of_rat_div_return_wit_1_r_eq_x : rat_div_return_wit_1_r_eq_x.
Axiom proof_of_rat_div_return_wit_2_r_eq_x : rat_div_return_wit_2_r_eq_x.
Axiom proof_of_rat_div_return_wit_3_r_eq_x : rat_div_return_wit_3_r_eq_x.
Axiom proof_of_rat_div_return_wit_4_r_eq_x : rat_div_return_wit_4_r_eq_x.
Axiom proof_of_rat_div_return_wit_5_out_undef : rat_div_return_wit_5_out_undef.
Axiom proof_of_rat_div_return_wit_6_out_undef : rat_div_return_wit_6_out_undef.
Axiom proof_of_rat_div_return_wit_7_out_undef : rat_div_return_wit_7_out_undef.
Axiom proof_of_rat_div_return_wit_8_out_undef : rat_div_return_wit_8_out_undef.
Axiom proof_of_rat_div_return_wit_9_out_known : rat_div_return_wit_9_out_known.
Axiom proof_of_rat_div_return_wit_10_out_known : rat_div_return_wit_10_out_known.
Axiom proof_of_rat_div_return_wit_11_out_known : rat_div_return_wit_11_out_known.
Axiom proof_of_rat_div_return_wit_12_out_known : rat_div_return_wit_12_out_known.
Axiom proof_of_rat_div_return_wit_13_r_eq_x : rat_div_return_wit_13_r_eq_x.
Axiom proof_of_rat_div_return_wit_14_r_eq_x : rat_div_return_wit_14_r_eq_x.
Axiom proof_of_rat_div_return_wit_15_r_eq_x : rat_div_return_wit_15_r_eq_x.
Axiom proof_of_rat_div_return_wit_16_r_eq_x : rat_div_return_wit_16_r_eq_x.
Axiom proof_of_rat_div_return_wit_17_out_undef : rat_div_return_wit_17_out_undef.
Axiom proof_of_rat_div_return_wit_18_out_undef : rat_div_return_wit_18_out_undef.
Axiom proof_of_rat_div_return_wit_19_out_undef : rat_div_return_wit_19_out_undef.
Axiom proof_of_rat_div_return_wit_20_out_undef : rat_div_return_wit_20_out_undef.
Axiom proof_of_rat_div_return_wit_21_out_known : rat_div_return_wit_21_out_known.
Axiom proof_of_rat_div_return_wit_22_out_known : rat_div_return_wit_22_out_known.
Axiom proof_of_rat_div_return_wit_23_out_known : rat_div_return_wit_23_out_known.
Axiom proof_of_rat_div_return_wit_24_out_known : rat_div_return_wit_24_out_known.
Axiom proof_of_rat_div_return_wit_25_r_eq_x : rat_div_return_wit_25_r_eq_x.
Axiom proof_of_rat_div_return_wit_26_out_undef : rat_div_return_wit_26_out_undef.
Axiom proof_of_rat_div_return_wit_27_out_known : rat_div_return_wit_27_out_known.
Axiom proof_of_rat_div_return_wit_28_r_eq_x : rat_div_return_wit_28_r_eq_x.
Axiom proof_of_rat_div_return_wit_29_out_undef : rat_div_return_wit_29_out_undef.
Axiom proof_of_rat_div_return_wit_30_out_known : rat_div_return_wit_30_out_known.
Axiom proof_of_rat_div_return_wit_31_r_eq_x : rat_div_return_wit_31_r_eq_x.
Axiom proof_of_rat_div_return_wit_32_out_undef : rat_div_return_wit_32_out_undef.
Axiom proof_of_rat_div_return_wit_33_out_known : rat_div_return_wit_33_out_known.
Axiom proof_of_rat_div_partial_solve_wit_1_r_eq_x_pure : rat_div_partial_solve_wit_1_r_eq_x_pure.
Axiom proof_of_rat_div_partial_solve_wit_1_r_eq_x : rat_div_partial_solve_wit_1_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_2_out_undef_pure : rat_div_partial_solve_wit_2_out_undef_pure.
Axiom proof_of_rat_div_partial_solve_wit_2_out_undef : rat_div_partial_solve_wit_2_out_undef.
Axiom proof_of_rat_div_partial_solve_wit_3_out_known_pure : rat_div_partial_solve_wit_3_out_known_pure.
Axiom proof_of_rat_div_partial_solve_wit_3_out_known : rat_div_partial_solve_wit_3_out_known.
Axiom proof_of_rat_div_partial_solve_wit_4_r_eq_x_pure : rat_div_partial_solve_wit_4_r_eq_x_pure.
Axiom proof_of_rat_div_partial_solve_wit_4_r_eq_x : rat_div_partial_solve_wit_4_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_5_out_undef_pure : rat_div_partial_solve_wit_5_out_undef_pure.
Axiom proof_of_rat_div_partial_solve_wit_5_out_undef : rat_div_partial_solve_wit_5_out_undef.
Axiom proof_of_rat_div_partial_solve_wit_6_out_known_pure : rat_div_partial_solve_wit_6_out_known_pure.
Axiom proof_of_rat_div_partial_solve_wit_6_out_known : rat_div_partial_solve_wit_6_out_known.
Axiom proof_of_rat_div_partial_solve_wit_7_r_eq_x : rat_div_partial_solve_wit_7_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_8_r_eq_x : rat_div_partial_solve_wit_8_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_9_r_eq_x : rat_div_partial_solve_wit_9_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_10_r_eq_x : rat_div_partial_solve_wit_10_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_11_r_eq_x_pure : rat_div_partial_solve_wit_11_r_eq_x_pure.
Axiom proof_of_rat_div_partial_solve_wit_11_r_eq_x : rat_div_partial_solve_wit_11_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_12_out_undef_pure : rat_div_partial_solve_wit_12_out_undef_pure.
Axiom proof_of_rat_div_partial_solve_wit_12_out_undef : rat_div_partial_solve_wit_12_out_undef.
Axiom proof_of_rat_div_partial_solve_wit_13_out_known_pure : rat_div_partial_solve_wit_13_out_known_pure.
Axiom proof_of_rat_div_partial_solve_wit_13_out_known : rat_div_partial_solve_wit_13_out_known.
Axiom proof_of_rat_div_partial_solve_wit_14_r_eq_x_pure : rat_div_partial_solve_wit_14_r_eq_x_pure.
Axiom proof_of_rat_div_partial_solve_wit_14_r_eq_x : rat_div_partial_solve_wit_14_r_eq_x.
Axiom proof_of_rat_div_partial_solve_wit_15_out_undef_pure : rat_div_partial_solve_wit_15_out_undef_pure.
Axiom proof_of_rat_div_partial_solve_wit_15_out_undef : rat_div_partial_solve_wit_15_out_undef.
Axiom proof_of_rat_div_partial_solve_wit_16_out_known_pure : rat_div_partial_solve_wit_16_out_known_pure.
Axiom proof_of_rat_div_partial_solve_wit_16_out_known : rat_div_partial_solve_wit_16_out_known.

End VC_Correct.
