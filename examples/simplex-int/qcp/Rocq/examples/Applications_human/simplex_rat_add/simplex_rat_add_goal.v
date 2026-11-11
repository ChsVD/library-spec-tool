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
Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib.
Local Open Scope sac.

(*----- Function rat_add -----*)

Definition rat_add_safety_wit_1_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_2_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_3_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_4_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_5_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_6_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 1)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_7_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_8_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_9_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_10_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
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
  “ False ”
.

Definition rat_add_safety_wit_11_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
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
  “ False ”
.

Definition rat_add_safety_wit_12_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
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
  “ False ”
.

Definition rat_add_safety_wit_13_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
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
  “ False ”
.

Definition rat_add_safety_wit_14_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_15_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_16_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_17_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_18_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
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

Definition rat_add_safety_wit_19_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_20_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_21_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_22_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_23_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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

Definition rat_add_safety_wit_24_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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

Definition rat_add_safety_wit_25_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_26_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_27_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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

Definition rat_add_safety_wit_28_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_29_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_30_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_31_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_32_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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

Definition rat_add_safety_wit_33_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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

Definition rat_add_safety_wit_34_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_35_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_36_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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

Definition rat_add_safety_wit_37_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_38_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH11 : (Q = (B_out_known * E_out_known ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_known)) (PreH25 : (A_out_known <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_known)) (PreH27 : (C_out_known <= INT_MAX)) (PreH28 : (1 <= B_out_known)) (PreH29 : (B_out_known <= INT_MAX)) (PreH30 : (1 <= E_out_known)) (PreH31 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_39_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_known)) (PreH23 : (A_out_known <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_known)) (PreH25 : (C_out_known <= INT_MAX)) (PreH26 : (1 <= B_out_known)) (PreH27 : (B_out_known <= INT_MAX)) (PreH28 : (1 <= E_out_known)) (PreH29 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_40_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : (P = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH10 : (Q = (B_out_known * E_out_known ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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

Definition rat_add_safety_wit_41_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_42_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH11 : (Q = (B_out_undef * E_out_undef ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_undef)) (PreH25 : (A_out_undef <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_undef)) (PreH27 : (C_out_undef <= INT_MAX)) (PreH28 : (1 <= B_out_undef)) (PreH29 : (B_out_undef <= INT_MAX)) (PreH30 : (1 <= E_out_undef)) (PreH31 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_43_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_undef)) (PreH23 : (A_out_undef <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_undef)) (PreH25 : (C_out_undef <= INT_MAX)) (PreH26 : (1 <= B_out_undef)) (PreH27 : (B_out_undef <= INT_MAX)) (PreH28 : (1 <= E_out_undef)) (PreH29 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_44_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : (P = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH10 : (Q = (B_out_undef * E_out_undef ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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

Definition rat_add_safety_wit_45_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_add_safety_wit_46_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH11 : (Q = (B_r_eq_x * E_r_eq_x ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH23 : (retval = 1)) (PreH24 : (out_pre = x_pre)) (PreH25 : ((-INT_MAX) <= A_r_eq_x)) (PreH26 : (A_r_eq_x <= INT_MAX)) (PreH27 : ((-INT_MAX) <= C_r_eq_x)) (PreH28 : (C_r_eq_x <= INT_MAX)) (PreH29 : (1 <= B_r_eq_x)) (PreH30 : (B_r_eq_x <= INT_MAX)) (PreH31 : (1 <= E_r_eq_x)) (PreH32 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_add_safety_wit_47_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH21 : (retval = 1)) (PreH22 : (out_pre = x_pre)) (PreH23 : ((-INT_MAX) <= A_r_eq_x)) (PreH24 : (A_r_eq_x <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_r_eq_x)) (PreH26 : (C_r_eq_x <= INT_MAX)) (PreH27 : (1 <= B_r_eq_x)) (PreH28 : (B_r_eq_x <= INT_MAX)) (PreH29 : (1 <= E_r_eq_x)) (PreH30 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_add_safety_wit_48_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : (P = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH10 : (Q = (B_r_eq_x * E_r_eq_x ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_add_return_wit_1_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) )) ” 
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
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_1_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_add_return_wit_1_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known 0 1 )
.

Definition rat_add_return_wit_1_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_2_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH11 : (Q_2 = (B_out_known * E_out_known ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_known)) (PreH25 : (A_out_known <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_known)) (PreH27 : (C_out_known <= INT_MAX)) (PreH28 : (1 <= B_out_known)) (PreH29 : (B_out_known <= INT_MAX)) (PreH30 : (1 <= E_out_known)) (PreH31 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) )) ” 
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
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH11 : (Q_2 = (B_out_known * E_out_known ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_known)) (PreH25 : (A_out_known <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_known)) (PreH27 : (C_out_known <= INT_MAX)) (PreH28 : (1 <= B_out_known)) (PreH29 : (B_out_known <= INT_MAX)) (PreH30 : (1 <= E_out_known)) (PreH31 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_2_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH11 : (Q_2 = (B_out_known * E_out_known ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_known)) (PreH25 : (A_out_known <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_known)) (PreH27 : (C_out_known <= INT_MAX)) (PreH28 : (1 <= B_out_known)) (PreH29 : (B_out_known <= INT_MAX)) (PreH30 : (1 <= E_out_known)) (PreH31 : (E_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_add_return_wit_2_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH11 : (Q_2 = (B_out_known * E_out_known ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_known)) (PreH25 : (A_out_known <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_known)) (PreH27 : (C_out_known <= INT_MAX)) (PreH28 : (1 <= B_out_known)) (PreH29 : (B_out_known <= INT_MAX)) (PreH30 : (1 <= E_out_known)) (PreH31 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known 0 1 )
.

Definition rat_add_return_wit_2_out_known_split_goal_3 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH11 : (Q_2 = (B_out_known * E_out_known ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_known)) (PreH25 : (A_out_known <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_known)) (PreH27 : (C_out_known <= INT_MAX)) (PreH28 : (1 <= B_out_known)) (PreH29 : (B_out_known <= INT_MAX)) (PreH30 : (1 <= E_out_known)) (PreH31 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_3_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_known)) (PreH23 : (A_out_known <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_known)) (PreH25 : (C_out_known <= INT_MAX)) (PreH26 : (1 <= B_out_known)) (PreH27 : (B_out_known <= INT_MAX)) (PreH28 : (1 <= E_out_known)) (PreH29 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) )) ” 
  &&  “ (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_known)) (PreH23 : (A_out_known <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_known)) (PreH25 : (C_out_known <= INT_MAX)) (PreH26 : (1 <= B_out_known)) (PreH27 : (B_out_known <= INT_MAX)) (PreH28 : (1 <= E_out_known)) (PreH29 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_3_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_known)) (PreH23 : (A_out_known <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_known)) (PreH25 : (C_out_known <= INT_MAX)) (PreH26 : (1 <= B_out_known)) (PreH27 : (B_out_known <= INT_MAX)) (PreH28 : (1 <= E_out_known)) (PreH29 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known P_2 Q_2 )
.

Definition rat_add_return_wit_3_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )))) ((B_out_known * E_out_known ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_known)) (PreH23 : (A_out_known <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_known)) (PreH25 : (C_out_known <= INT_MAX)) (PreH26 : (1 <= B_out_known)) (PreH27 : (B_out_known <= INT_MAX)) (PreH28 : (1 <= E_out_known)) (PreH29 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_4_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH10 : (Q_2 = (B_out_known * E_out_known ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q ) = (P * (B_out_known * E_out_known ) )) ” 
  &&  “ (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH10 : (Q_2 = (B_out_known * E_out_known ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_4_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH10 : (Q_2 = (B_out_known * E_out_known ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  (simplex_rat_add_result A_out_known B_out_known C_out_known E_out_known ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) )
.

Definition rat_add_return_wit_4_out_known_split_goal_2 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) (B_out_known * E_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) * Q_2 ) = (P_2 * (B_out_known * E_out_known ) ))) (PreH8 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <> 0)) (PreH9 : (P_2 = ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))) (PreH10 : (Q_2 = (B_out_known * E_out_known ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_known)) (PreH24 : (A_out_known <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_known)) (PreH26 : (C_out_known <= INT_MAX)) (PreH27 : (1 <= B_out_known)) (PreH28 : (B_out_known <= INT_MAX)) (PreH29 : (1 <= E_out_known)) (PreH30 : (E_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_5_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) )) ” 
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
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_5_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_add_return_wit_5_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 )
.

Definition rat_add_return_wit_5_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_6_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH11 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_undef)) (PreH25 : (A_out_undef <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_undef)) (PreH27 : (C_out_undef <= INT_MAX)) (PreH28 : (1 <= B_out_undef)) (PreH29 : (B_out_undef <= INT_MAX)) (PreH30 : (1 <= E_out_undef)) (PreH31 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) )) ” 
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
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH11 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_undef)) (PreH25 : (A_out_undef <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_undef)) (PreH27 : (C_out_undef <= INT_MAX)) (PreH28 : (1 <= B_out_undef)) (PreH29 : (B_out_undef <= INT_MAX)) (PreH30 : (1 <= E_out_undef)) (PreH31 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_6_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH11 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_undef)) (PreH25 : (A_out_undef <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_undef)) (PreH27 : (C_out_undef <= INT_MAX)) (PreH28 : (1 <= B_out_undef)) (PreH29 : (B_out_undef <= INT_MAX)) (PreH30 : (1 <= E_out_undef)) (PreH31 : (E_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_add_return_wit_6_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH11 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_undef)) (PreH25 : (A_out_undef <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_undef)) (PreH27 : (C_out_undef <= INT_MAX)) (PreH28 : (1 <= B_out_undef)) (PreH29 : (B_out_undef <= INT_MAX)) (PreH30 : (1 <= E_out_undef)) (PreH31 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef 0 1 )
.

Definition rat_add_return_wit_6_out_undef_split_goal_3 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH11 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH23 : (retval = 1)) (PreH24 : ((-INT_MAX) <= A_out_undef)) (PreH25 : (A_out_undef <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_out_undef)) (PreH27 : (C_out_undef <= INT_MAX)) (PreH28 : (1 <= B_out_undef)) (PreH29 : (B_out_undef <= INT_MAX)) (PreH30 : (1 <= E_out_undef)) (PreH31 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_7_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_undef)) (PreH23 : (A_out_undef <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_undef)) (PreH25 : (C_out_undef <= INT_MAX)) (PreH26 : (1 <= B_out_undef)) (PreH27 : (B_out_undef <= INT_MAX)) (PreH28 : (1 <= E_out_undef)) (PreH29 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) )) ” 
  &&  “ (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_undef)) (PreH23 : (A_out_undef <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_undef)) (PreH25 : (C_out_undef <= INT_MAX)) (PreH26 : (1 <= B_out_undef)) (PreH27 : (B_out_undef <= INT_MAX)) (PreH28 : (1 <= E_out_undef)) (PreH29 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_7_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_undef)) (PreH23 : (A_out_undef <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_undef)) (PreH25 : (C_out_undef <= INT_MAX)) (PreH26 : (1 <= B_out_undef)) (PreH27 : (B_out_undef <= INT_MAX)) (PreH28 : (1 <= E_out_undef)) (PreH29 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef P_2 Q_2 )
.

Definition rat_add_return_wit_7_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )))) ((B_out_undef * E_out_undef ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH21 : (retval = 1)) (PreH22 : ((-INT_MAX) <= A_out_undef)) (PreH23 : (A_out_undef <= INT_MAX)) (PreH24 : ((-INT_MAX) <= C_out_undef)) (PreH25 : (C_out_undef <= INT_MAX)) (PreH26 : (1 <= B_out_undef)) (PreH27 : (B_out_undef <= INT_MAX)) (PreH28 : (1 <= E_out_undef)) (PreH29 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_8_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH10 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q ) = (P * (B_out_undef * E_out_undef ) )) ” 
  &&  “ (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH10 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_8_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH10 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  (simplex_rat_add_result A_out_undef B_out_undef C_out_undef E_out_undef ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) )
.

Definition rat_add_return_wit_8_out_undef_split_goal_2 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) (B_out_undef * E_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) * Q_2 ) = (P_2 * (B_out_undef * E_out_undef ) ))) (PreH8 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <> 0)) (PreH9 : (P_2 = ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))) (PreH10 : (Q_2 = (B_out_undef * E_out_undef ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH22 : (retval = 1)) (PreH23 : ((-INT_MAX) <= A_out_undef)) (PreH24 : (A_out_undef <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_out_undef)) (PreH26 : (C_out_undef <= INT_MAX)) (PreH27 : (1 <= B_out_undef)) (PreH28 : (B_out_undef <= INT_MAX)) (PreH29 : (1 <= E_out_undef)) (PreH30 : (E_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_9_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_9_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_add_return_wit_9_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 )
.

Definition rat_add_return_wit_9_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_10_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH11 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH23 : (retval = 1)) (PreH24 : (out_pre = x_pre)) (PreH25 : ((-INT_MAX) <= A_r_eq_x)) (PreH26 : (A_r_eq_x <= INT_MAX)) (PreH27 : ((-INT_MAX) <= C_r_eq_x)) (PreH28 : (C_r_eq_x <= INT_MAX)) (PreH29 : (1 <= B_r_eq_x)) (PreH30 : (B_r_eq_x <= INT_MAX)) (PreH31 : (1 <= E_r_eq_x)) (PreH32 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH11 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH23 : (retval = 1)) (PreH24 : (out_pre = x_pre)) (PreH25 : ((-INT_MAX) <= A_r_eq_x)) (PreH26 : (A_r_eq_x <= INT_MAX)) (PreH27 : ((-INT_MAX) <= C_r_eq_x)) (PreH28 : (C_r_eq_x <= INT_MAX)) (PreH29 : (1 <= B_r_eq_x)) (PreH30 : (B_r_eq_x <= INT_MAX)) (PreH31 : (1 <= E_r_eq_x)) (PreH32 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_10_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH11 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH23 : (retval = 1)) (PreH24 : (out_pre = x_pre)) (PreH25 : ((-INT_MAX) <= A_r_eq_x)) (PreH26 : (A_r_eq_x <= INT_MAX)) (PreH27 : ((-INT_MAX) <= C_r_eq_x)) (PreH28 : (C_r_eq_x <= INT_MAX)) (PreH29 : (1 <= B_r_eq_x)) (PreH30 : (B_r_eq_x <= INT_MAX)) (PreH31 : (1 <= E_r_eq_x)) (PreH32 : (E_r_eq_x <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_add_return_wit_10_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH11 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH23 : (retval = 1)) (PreH24 : (out_pre = x_pre)) (PreH25 : ((-INT_MAX) <= A_r_eq_x)) (PreH26 : (A_r_eq_x <= INT_MAX)) (PreH27 : ((-INT_MAX) <= C_r_eq_x)) (PreH28 : (C_r_eq_x <= INT_MAX)) (PreH29 : (1 <= B_r_eq_x)) (PreH30 : (B_r_eq_x <= INT_MAX)) (PreH31 : (1 <= E_r_eq_x)) (PreH32 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x 0 1 )
.

Definition rat_add_return_wit_10_r_eq_x_split_goal_3 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH11 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH12 : (retval_4 <> 0)) (PreH13 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH14 : (retval_4 = 1)) (PreH15 : (retval_3 <> 0)) (PreH16 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH17 : (retval_3 = 1)) (PreH18 : (retval_2 <> 0)) (PreH19 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH20 : (retval_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH23 : (retval = 1)) (PreH24 : (out_pre = x_pre)) (PreH25 : ((-INT_MAX) <= A_r_eq_x)) (PreH26 : (A_r_eq_x <= INT_MAX)) (PreH27 : ((-INT_MAX) <= C_r_eq_x)) (PreH28 : (C_r_eq_x <= INT_MAX)) (PreH29 : (1 <= B_r_eq_x)) (PreH30 : (B_r_eq_x <= INT_MAX)) (PreH31 : (1 <= E_r_eq_x)) (PreH32 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_11_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH21 : (retval = 1)) (PreH22 : (out_pre = x_pre)) (PreH23 : ((-INT_MAX) <= A_r_eq_x)) (PreH24 : (A_r_eq_x <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_r_eq_x)) (PreH26 : (C_r_eq_x <= INT_MAX)) (PreH27 : (1 <= B_r_eq_x)) (PreH28 : (B_r_eq_x <= INT_MAX)) (PreH29 : (1 <= E_r_eq_x)) (PreH30 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) )) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH21 : (retval = 1)) (PreH22 : (out_pre = x_pre)) (PreH23 : ((-INT_MAX) <= A_r_eq_x)) (PreH24 : (A_r_eq_x <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_r_eq_x)) (PreH26 : (C_r_eq_x <= INT_MAX)) (PreH27 : (1 <= B_r_eq_x)) (PreH28 : (B_r_eq_x <= INT_MAX)) (PreH29 : (1 <= E_r_eq_x)) (PreH30 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_11_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH21 : (retval = 1)) (PreH22 : (out_pre = x_pre)) (PreH23 : ((-INT_MAX) <= A_r_eq_x)) (PreH24 : (A_r_eq_x <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_r_eq_x)) (PreH26 : (C_r_eq_x <= INT_MAX)) (PreH27 : (1 <= B_r_eq_x)) (PreH28 : (B_r_eq_x <= INT_MAX)) (PreH29 : (1 <= E_r_eq_x)) (PreH30 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P_2 Q_2 )
.

Definition rat_add_return_wit_11_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : ((Zgcd ((Zabs (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )))) ((B_r_eq_x * E_r_eq_x ))) <> 1)) (PreH10 : (retval_4 <> 0)) (PreH11 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval_4 = 1)) (PreH13 : (retval_3 <> 0)) (PreH14 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH15 : (retval_3 = 1)) (PreH16 : (retval_2 <> 0)) (PreH17 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH18 : (retval_2 = 1)) (PreH19 : (retval <> 0)) (PreH20 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH21 : (retval = 1)) (PreH22 : (out_pre = x_pre)) (PreH23 : ((-INT_MAX) <= A_r_eq_x)) (PreH24 : (A_r_eq_x <= INT_MAX)) (PreH25 : ((-INT_MAX) <= C_r_eq_x)) (PreH26 : (C_r_eq_x <= INT_MAX)) (PreH27 : (1 <= B_r_eq_x)) (PreH28 : (B_r_eq_x <= INT_MAX)) (PreH29 : (1 <= E_r_eq_x)) (PreH30 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_12_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH10 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q ) = (P * (B_r_eq_x * E_r_eq_x ) )) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH10 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) ) ” 
  &&  “ (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_12_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH10 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  (simplex_rat_add_result A_r_eq_x B_r_eq_x C_r_eq_x E_r_eq_x ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) )
.

Definition rat_add_return_wit_12_r_eq_x_split_goal_2 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) (B_r_eq_x * E_r_eq_x ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : ((((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) * Q_2 ) = (P_2 * (B_r_eq_x * E_r_eq_x ) ))) (PreH8 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <> 0)) (PreH9 : (P_2 = ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))) (PreH10 : (Q_2 = (B_r_eq_x * E_r_eq_x ))) (PreH11 : (retval_4 <> 0)) (PreH12 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH13 : (retval_4 = 1)) (PreH14 : (retval_3 <> 0)) (PreH15 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH16 : (retval_3 = 1)) (PreH17 : (retval_2 <> 0)) (PreH18 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH19 : (retval_2 = 1)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH22 : (retval = 1)) (PreH23 : (out_pre = x_pre)) (PreH24 : ((-INT_MAX) <= A_r_eq_x)) (PreH25 : (A_r_eq_x <= INT_MAX)) (PreH26 : ((-INT_MAX) <= C_r_eq_x)) (PreH27 : (C_r_eq_x <= INT_MAX)) (PreH28 : (1 <= B_r_eq_x)) (PreH29 : (B_r_eq_x <= INT_MAX)) (PreH30 : (1 <= E_r_eq_x)) (PreH31 : (E_r_eq_x <= INT_MAX)) ,
  (1 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_13_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_13_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_14_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_14_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_15_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_15_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 = 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_16_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_16_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_17_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_17_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_18_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_18_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 = 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_19_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_19_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_20_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_20_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_21_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_21_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_return_wit_22_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known))) ”
  &&  emp
).

Definition rat_add_return_wit_22_out_known_split_goal_1 := 
forall (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_known) (B_out_known) (C_out_known) (E_out_known)))
.

Definition rat_add_return_wit_23_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef))) ”
  &&  emp
).

Definition rat_add_return_wit_23_out_undef_split_goal_1 := 
forall (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_out_undef) (B_out_undef) (C_out_undef) (E_out_undef)))
.

Definition rat_add_return_wit_24_r_eq_x := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
) \/
(
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x))) ”
  &&  emp
).

Definition rat_add_return_wit_24_r_eq_x_split_goal_1 := 
forall (out_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 0)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  (0 = (simplex_rat_add_flag (A_r_eq_x) (B_r_eq_x) (C_r_eq_x) (E_r_eq_x)))
.

Definition rat_add_partial_solve_wit_1_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-INT_MAX) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((-INT_MAX) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= E_out_known)) (PreH8 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
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

Definition rat_add_partial_solve_wit_1_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((-INT_MAX) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((-INT_MAX) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= E_out_known)) (PreH8 : (E_out_known <= INT_MAX)) ,
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

Definition rat_add_partial_solve_wit_1_out_known := rat_add_partial_solve_wit_1_out_known_pure -> rat_add_partial_solve_wit_1_out_known_aux.

Definition rat_add_partial_solve_wit_2_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-INT_MAX) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((-INT_MAX) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= E_out_undef)) (PreH8 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
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

Definition rat_add_partial_solve_wit_2_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((-INT_MAX) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((-INT_MAX) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= E_out_undef)) (PreH8 : (E_out_undef <= INT_MAX)) ,
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

Definition rat_add_partial_solve_wit_2_out_undef := rat_add_partial_solve_wit_2_out_undef_pure -> rat_add_partial_solve_wit_2_out_undef_aux.

Definition rat_add_partial_solve_wit_3_r_eq_x_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (out_pre = x_pre)) (PreH2 : ((-INT_MAX) <= A_r_eq_x)) (PreH3 : (A_r_eq_x <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_r_eq_x)) (PreH5 : (C_r_eq_x <= INT_MAX)) (PreH6 : (1 <= B_r_eq_x)) (PreH7 : (B_r_eq_x <= INT_MAX)) (PreH8 : (1 <= E_r_eq_x)) (PreH9 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
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

Definition rat_add_partial_solve_wit_3_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (PreH1 : (out_pre = x_pre)) (PreH2 : ((-INT_MAX) <= A_r_eq_x)) (PreH3 : (A_r_eq_x <= INT_MAX)) (PreH4 : ((-INT_MAX) <= C_r_eq_x)) (PreH5 : (C_r_eq_x <= INT_MAX)) (PreH6 : (1 <= B_r_eq_x)) (PreH7 : (B_r_eq_x <= INT_MAX)) (PreH8 : (1 <= E_r_eq_x)) (PreH9 : (E_r_eq_x <= INT_MAX)) ,
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

Definition rat_add_partial_solve_wit_3_r_eq_x := rat_add_partial_solve_wit_3_r_eq_x_pure -> rat_add_partial_solve_wit_3_r_eq_x_aux.

Definition rat_add_partial_solve_wit_4_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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
  “ (C_out_known = C_out_known) ” 
  &&  “ (B_out_known = B_out_known) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ”
.

Definition rat_add_partial_solve_wit_4_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((-INT_MAX) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= E_out_known)) (PreH11 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (C_out_known = C_out_known) ” 
  &&  “ (B_out_known = B_out_known) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_4_out_known := rat_add_partial_solve_wit_4_out_known_pure -> rat_add_partial_solve_wit_4_out_known_aux.

Definition rat_add_partial_solve_wit_5_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
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
  “ (C_out_undef = C_out_undef) ” 
  &&  “ (B_out_undef = B_out_undef) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ”
.

Definition rat_add_partial_solve_wit_5_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((-INT_MAX) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((-INT_MAX) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= E_out_undef)) (PreH11 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (C_out_undef = C_out_undef) ” 
  &&  “ (B_out_undef = B_out_undef) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_5_out_undef := rat_add_partial_solve_wit_5_out_undef_pure -> rat_add_partial_solve_wit_5_out_undef_aux.

Definition rat_add_partial_solve_wit_6_r_eq_x_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 1)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (C_r_eq_x = C_r_eq_x) ” 
  &&  “ (B_r_eq_x = B_r_eq_x) ” 
  &&  “ ((INT_MIN) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ”
.

Definition rat_add_partial_solve_wit_6_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval = 1)) (PreH4 : (out_pre = x_pre)) (PreH5 : ((-INT_MAX) <= A_r_eq_x)) (PreH6 : (A_r_eq_x <= INT_MAX)) (PreH7 : ((-INT_MAX) <= C_r_eq_x)) (PreH8 : (C_r_eq_x <= INT_MAX)) (PreH9 : (1 <= B_r_eq_x)) (PreH10 : (B_r_eq_x <= INT_MAX)) (PreH11 : (1 <= E_r_eq_x)) (PreH12 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (C_r_eq_x = C_r_eq_x) ” 
  &&  “ (B_r_eq_x = B_r_eq_x) ” 
  &&  “ ((INT_MIN) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_6_r_eq_x := rat_add_partial_solve_wit_6_r_eq_x_pure -> rat_add_partial_solve_wit_6_r_eq_x_aux.

Definition rat_add_partial_solve_wit_7_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
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
  “ ((A_out_known * E_out_known ) = (A_out_known * E_out_known )) ” 
  &&  “ ((C_out_known * B_out_known ) = (C_out_known * B_out_known )) ” 
  &&  “ ((C_out_known * B_out_known ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (C_out_known * B_out_known )) ” 
  &&  “ ((A_out_known * E_out_known ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (A_out_known * E_out_known )) ”
.

Definition rat_add_partial_solve_wit_7_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= E_out_known)) (PreH14 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ ((A_out_known * E_out_known ) = (A_out_known * E_out_known )) ” 
  &&  “ ((C_out_known * B_out_known ) = (C_out_known * B_out_known )) ” 
  &&  “ ((C_out_known * B_out_known ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (C_out_known * B_out_known )) ” 
  &&  “ ((A_out_known * E_out_known ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (A_out_known * E_out_known )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_out_known) (B_out_known))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_7_out_known := rat_add_partial_solve_wit_7_out_known_pure -> rat_add_partial_solve_wit_7_out_known_aux.

Definition rat_add_partial_solve_wit_8_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
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
  “ ((A_out_undef * E_out_undef ) = (A_out_undef * E_out_undef )) ” 
  &&  “ ((C_out_undef * B_out_undef ) = (C_out_undef * B_out_undef )) ” 
  &&  “ ((C_out_undef * B_out_undef ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (C_out_undef * B_out_undef )) ” 
  &&  “ ((A_out_undef * E_out_undef ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (A_out_undef * E_out_undef )) ”
.

Definition rat_add_partial_solve_wit_8_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((-INT_MAX) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((-INT_MAX) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= E_out_undef)) (PreH14 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ ((A_out_undef * E_out_undef ) = (A_out_undef * E_out_undef )) ” 
  &&  “ ((C_out_undef * B_out_undef ) = (C_out_undef * B_out_undef )) ” 
  &&  “ ((C_out_undef * B_out_undef ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (C_out_undef * B_out_undef )) ” 
  &&  “ ((A_out_undef * E_out_undef ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (A_out_undef * E_out_undef )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_8_out_undef := rat_add_partial_solve_wit_8_out_undef_pure -> rat_add_partial_solve_wit_8_out_undef_aux.

Definition rat_add_partial_solve_wit_9_r_eq_x_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((A_r_eq_x * E_r_eq_x ) = (A_r_eq_x * E_r_eq_x )) ” 
  &&  “ ((C_r_eq_x * B_r_eq_x ) = (C_r_eq_x * B_r_eq_x )) ” 
  &&  “ ((C_r_eq_x * B_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (C_r_eq_x * B_r_eq_x )) ” 
  &&  “ ((A_r_eq_x * E_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (A_r_eq_x * E_r_eq_x )) ”
.

Definition rat_add_partial_solve_wit_9_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH6 : (retval = 1)) (PreH7 : (out_pre = x_pre)) (PreH8 : ((-INT_MAX) <= A_r_eq_x)) (PreH9 : (A_r_eq_x <= INT_MAX)) (PreH10 : ((-INT_MAX) <= C_r_eq_x)) (PreH11 : (C_r_eq_x <= INT_MAX)) (PreH12 : (1 <= B_r_eq_x)) (PreH13 : (B_r_eq_x <= INT_MAX)) (PreH14 : (1 <= E_r_eq_x)) (PreH15 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((A_r_eq_x * E_r_eq_x ) = (A_r_eq_x * E_r_eq_x )) ” 
  &&  “ ((C_r_eq_x * B_r_eq_x ) = (C_r_eq_x * B_r_eq_x )) ” 
  &&  “ ((C_r_eq_x * B_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (C_r_eq_x * B_r_eq_x )) ” 
  &&  “ ((A_r_eq_x * E_r_eq_x ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (A_r_eq_x * E_r_eq_x )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_9_r_eq_x := rat_add_partial_solve_wit_9_r_eq_x_pure -> rat_add_partial_solve_wit_9_r_eq_x_aux.

Definition rat_add_partial_solve_wit_10_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
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
  &&  “ (E_out_known = E_out_known) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
.

Definition rat_add_partial_solve_wit_10_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_known)) (PreH11 : (A_out_known <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_known)) (PreH13 : (C_out_known <= INT_MAX)) (PreH14 : (1 <= B_out_known)) (PreH15 : (B_out_known <= INT_MAX)) (PreH16 : (1 <= E_out_known)) (PreH17 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (B_out_known = B_out_known) ” 
  &&  “ (E_out_known = E_out_known) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_out_known) (B_out_known))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_10_out_known := rat_add_partial_solve_wit_10_out_known_pure -> rat_add_partial_solve_wit_10_out_known_aux.

Definition rat_add_partial_solve_wit_11_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
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
  &&  “ (E_out_undef = E_out_undef) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
.

Definition rat_add_partial_solve_wit_11_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH9 : (retval = 1)) (PreH10 : ((-INT_MAX) <= A_out_undef)) (PreH11 : (A_out_undef <= INT_MAX)) (PreH12 : ((-INT_MAX) <= C_out_undef)) (PreH13 : (C_out_undef <= INT_MAX)) (PreH14 : (1 <= B_out_undef)) (PreH15 : (B_out_undef <= INT_MAX)) (PreH16 : (1 <= E_out_undef)) (PreH17 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (B_out_undef = B_out_undef) ” 
  &&  “ (E_out_undef = E_out_undef) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_11_out_undef := rat_add_partial_solve_wit_11_out_undef_pure -> rat_add_partial_solve_wit_11_out_undef_aux.

Definition rat_add_partial_solve_wit_12_r_eq_x_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
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
  &&  “ (E_r_eq_x = E_r_eq_x) ” 
  &&  “ ((INT_MIN) <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
.

Definition rat_add_partial_solve_wit_12_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH3 : (retval_3 = 1)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH6 : (retval_2 = 1)) (PreH7 : (retval <> 0)) (PreH8 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH9 : (retval = 1)) (PreH10 : (out_pre = x_pre)) (PreH11 : ((-INT_MAX) <= A_r_eq_x)) (PreH12 : (A_r_eq_x <= INT_MAX)) (PreH13 : ((-INT_MAX) <= C_r_eq_x)) (PreH14 : (C_r_eq_x <= INT_MAX)) (PreH15 : (1 <= B_r_eq_x)) (PreH16 : (B_r_eq_x <= INT_MAX)) (PreH17 : (1 <= E_r_eq_x)) (PreH18 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (B_r_eq_x = B_r_eq_x) ” 
  &&  “ (E_r_eq_x = E_r_eq_x) ” 
  &&  “ ((INT_MIN) <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_12_r_eq_x := rat_add_partial_solve_wit_12_r_eq_x_pure -> rat_add_partial_solve_wit_12_r_eq_x_aux.

Definition rat_add_partial_solve_wit_13_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_r_eq_x)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
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

Definition rat_add_partial_solve_wit_14_r_eq_x := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
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
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_add_partial_solve_wit_15_out_known_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * E_out_known ))
|--
  “ (1 <= (B_out_known * E_out_known )) ” 
  &&  “ ((B_out_known * E_out_known ) <= INT_MAX) ” 
  &&  “ (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (E_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((A_out_known * E_out_known ) <= INT_MAX)) (PreH6 : ((C_out_known * B_out_known ) <= INT_MAX)) (PreH7 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <= INT_MAX)) (PreH8 : ((B_out_known * E_out_known ) <= INT_MAX)) (PreH9 : (E_out_known >= INT_MIN)) (PreH10 : (C_out_known >= INT_MIN)) (PreH11 : (B_out_known >= INT_MIN)) (PreH12 : (A_out_known >= INT_MIN)) (PreH13 : ((A_out_known * E_out_known ) >= INT_MIN)) (PreH14 : ((C_out_known * B_out_known ) >= INT_MIN)) (PreH15 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) >= INT_MIN)) (PreH16 : ((B_out_known * E_out_known ) >= INT_MIN)) (PreH17 : (retval_4 <> 0)) (PreH18 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH19 : (retval_4 = 1)) (PreH20 : (retval_3 <> 0)) (PreH21 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH22 : (retval_3 = 1)) (PreH23 : (retval_2 <> 0)) (PreH24 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH25 : (retval_2 = 1)) (PreH26 : (retval <> 0)) (PreH27 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH28 : (retval = 1)) (PreH29 : ((-INT_MAX) <= A_out_known)) (PreH30 : (A_out_known <= INT_MAX)) (PreH31 : ((-INT_MAX) <= C_out_known)) (PreH32 : (C_out_known <= INT_MAX)) (PreH33 : (1 <= B_out_known)) (PreH34 : (B_out_known <= INT_MAX)) (PreH35 : (1 <= E_out_known)) (PreH36 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * E_out_known ))
|--
  “ ((-INT_MAX) <= ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )) ”
).

Definition rat_add_partial_solve_wit_15_out_known_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (E_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((A_out_known * E_out_known ) <= INT_MAX)) (PreH6 : ((C_out_known * B_out_known ) <= INT_MAX)) (PreH7 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <= INT_MAX)) (PreH8 : ((B_out_known * E_out_known ) <= INT_MAX)) (PreH9 : (E_out_known >= INT_MIN)) (PreH10 : (C_out_known >= INT_MIN)) (PreH11 : (B_out_known >= INT_MIN)) (PreH12 : (A_out_known >= INT_MIN)) (PreH13 : ((A_out_known * E_out_known ) >= INT_MIN)) (PreH14 : ((C_out_known * B_out_known ) >= INT_MIN)) (PreH15 : (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) >= INT_MIN)) (PreH16 : ((B_out_known * E_out_known ) >= INT_MIN)) (PreH17 : (retval_4 <> 0)) (PreH18 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH19 : (retval_4 = 1)) (PreH20 : (retval_3 <> 0)) (PreH21 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH22 : (retval_3 = 1)) (PreH23 : (retval_2 <> 0)) (PreH24 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH25 : (retval_2 = 1)) (PreH26 : (retval <> 0)) (PreH27 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH28 : (retval = 1)) (PreH29 : ((-INT_MAX) <= A_out_known)) (PreH30 : (A_out_known <= INT_MAX)) (PreH31 : ((-INT_MAX) <= C_out_known)) (PreH32 : (C_out_known <= INT_MAX)) (PreH33 : (1 <= B_out_known)) (PreH34 : (B_out_known <= INT_MAX)) (PreH35 : (1 <= E_out_known)) (PreH36 : (E_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * E_out_known ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * E_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * E_out_known ))
|--
  “ ((-INT_MAX) <= ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )) ”
.

Definition rat_add_partial_solve_wit_15_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_known) (E_out_known)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_known) (E_out_known)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_known)) (PreH14 : (A_out_known <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_known)) (PreH16 : (C_out_known <= INT_MAX)) (PreH17 : (1 <= B_out_known)) (PreH18 : (B_out_known <= INT_MAX)) (PreH19 : (1 <= E_out_known)) (PreH20 : (E_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * E_out_known ))
|--
  “ (1 <= (B_out_known * E_out_known )) ” 
  &&  “ ((B_out_known * E_out_known ) <= INT_MAX) ” 
  &&  “ (((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) )) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (checked_mul_flag (B_out_known) (E_out_known))) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_out_known * E_out_known )) ((C_out_known * B_out_known )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_out_known) (B_out_known))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (E_out_known))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((-INT_MAX) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= E_out_known) ” 
  &&  “ (E_out_known <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_known * E_out_known ) + (C_out_known * B_out_known ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * E_out_known ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_known)
.

Definition rat_add_partial_solve_wit_15_out_known := rat_add_partial_solve_wit_15_out_known_pure -> rat_add_partial_solve_wit_15_out_known_aux.

Definition rat_add_partial_solve_wit_16_out_undef_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * E_out_undef ))
|--
  “ (1 <= (B_out_undef * E_out_undef )) ” 
  &&  “ ((B_out_undef * E_out_undef ) <= INT_MAX) ” 
  &&  “ (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (E_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((A_out_undef * E_out_undef ) <= INT_MAX)) (PreH6 : ((C_out_undef * B_out_undef ) <= INT_MAX)) (PreH7 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <= INT_MAX)) (PreH8 : ((B_out_undef * E_out_undef ) <= INT_MAX)) (PreH9 : (E_out_undef >= INT_MIN)) (PreH10 : (C_out_undef >= INT_MIN)) (PreH11 : (B_out_undef >= INT_MIN)) (PreH12 : (A_out_undef >= INT_MIN)) (PreH13 : ((A_out_undef * E_out_undef ) >= INT_MIN)) (PreH14 : ((C_out_undef * B_out_undef ) >= INT_MIN)) (PreH15 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) >= INT_MIN)) (PreH16 : ((B_out_undef * E_out_undef ) >= INT_MIN)) (PreH17 : (retval_4 <> 0)) (PreH18 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH19 : (retval_4 = 1)) (PreH20 : (retval_3 <> 0)) (PreH21 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH22 : (retval_3 = 1)) (PreH23 : (retval_2 <> 0)) (PreH24 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH25 : (retval_2 = 1)) (PreH26 : (retval <> 0)) (PreH27 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH28 : (retval = 1)) (PreH29 : ((-INT_MAX) <= A_out_undef)) (PreH30 : (A_out_undef <= INT_MAX)) (PreH31 : ((-INT_MAX) <= C_out_undef)) (PreH32 : (C_out_undef <= INT_MAX)) (PreH33 : (1 <= B_out_undef)) (PreH34 : (B_out_undef <= INT_MAX)) (PreH35 : (1 <= E_out_undef)) (PreH36 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * E_out_undef ))
|--
  “ ((-INT_MAX) <= ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )) ”
).

Definition rat_add_partial_solve_wit_16_out_undef_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (E_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((A_out_undef * E_out_undef ) <= INT_MAX)) (PreH6 : ((C_out_undef * B_out_undef ) <= INT_MAX)) (PreH7 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <= INT_MAX)) (PreH8 : ((B_out_undef * E_out_undef ) <= INT_MAX)) (PreH9 : (E_out_undef >= INT_MIN)) (PreH10 : (C_out_undef >= INT_MIN)) (PreH11 : (B_out_undef >= INT_MIN)) (PreH12 : (A_out_undef >= INT_MIN)) (PreH13 : ((A_out_undef * E_out_undef ) >= INT_MIN)) (PreH14 : ((C_out_undef * B_out_undef ) >= INT_MIN)) (PreH15 : (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) >= INT_MIN)) (PreH16 : ((B_out_undef * E_out_undef ) >= INT_MIN)) (PreH17 : (retval_4 <> 0)) (PreH18 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH19 : (retval_4 = 1)) (PreH20 : (retval_3 <> 0)) (PreH21 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH22 : (retval_3 = 1)) (PreH23 : (retval_2 <> 0)) (PreH24 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH25 : (retval_2 = 1)) (PreH26 : (retval <> 0)) (PreH27 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH28 : (retval = 1)) (PreH29 : ((-INT_MAX) <= A_out_undef)) (PreH30 : (A_out_undef <= INT_MAX)) (PreH31 : ((-INT_MAX) <= C_out_undef)) (PreH32 : (C_out_undef <= INT_MAX)) (PreH33 : (1 <= B_out_undef)) (PreH34 : (B_out_undef <= INT_MAX)) (PreH35 : (1 <= E_out_undef)) (PreH36 : (E_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * E_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * E_out_undef ))
|--
  “ ((-INT_MAX) <= ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )) ”
.

Definition rat_add_partial_solve_wit_16_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_out_undef) (E_out_undef)))) (PreH12 : (retval = 1)) (PreH13 : ((-INT_MAX) <= A_out_undef)) (PreH14 : (A_out_undef <= INT_MAX)) (PreH15 : ((-INT_MAX) <= C_out_undef)) (PreH16 : (C_out_undef <= INT_MAX)) (PreH17 : (1 <= B_out_undef)) (PreH18 : (B_out_undef <= INT_MAX)) (PreH19 : (1 <= E_out_undef)) (PreH20 : (E_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * E_out_undef ))
|--
  “ (1 <= (B_out_undef * E_out_undef )) ” 
  &&  “ ((B_out_undef * E_out_undef ) <= INT_MAX) ” 
  &&  “ (((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) )) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (checked_mul_flag (B_out_undef) (E_out_undef))) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_out_undef * E_out_undef )) ((C_out_undef * B_out_undef )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (E_out_undef))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((-INT_MAX) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= E_out_undef) ” 
  &&  “ (E_out_undef <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_out_undef * E_out_undef ) + (C_out_undef * B_out_undef ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * E_out_undef ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_out_undef)
.

Definition rat_add_partial_solve_wit_16_out_undef := rat_add_partial_solve_wit_16_out_undef_pure -> rat_add_partial_solve_wit_16_out_undef_aux.

Definition rat_add_partial_solve_wit_17_r_eq_x_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= (B_r_eq_x * E_r_eq_x )) ” 
  &&  “ ((B_r_eq_x * E_r_eq_x ) <= INT_MAX) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (E_r_eq_x <= INT_MAX)) (PreH2 : (C_r_eq_x <= INT_MAX)) (PreH3 : ((A_r_eq_x * E_r_eq_x ) <= INT_MAX)) (PreH4 : ((C_r_eq_x * B_r_eq_x ) <= INT_MAX)) (PreH5 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <= INT_MAX)) (PreH6 : ((B_r_eq_x * E_r_eq_x ) <= INT_MAX)) (PreH7 : (E_r_eq_x >= INT_MIN)) (PreH8 : (C_r_eq_x >= INT_MIN)) (PreH9 : ((A_r_eq_x * E_r_eq_x ) >= INT_MIN)) (PreH10 : ((C_r_eq_x * B_r_eq_x ) >= INT_MIN)) (PreH11 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) >= INT_MIN)) (PreH12 : ((B_r_eq_x * E_r_eq_x ) >= INT_MIN)) (PreH13 : (retval_4 <> 0)) (PreH14 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH15 : (retval_4 = 1)) (PreH16 : (retval_3 <> 0)) (PreH17 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH18 : (retval_3 = 1)) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH21 : (retval_2 = 1)) (PreH22 : (retval <> 0)) (PreH23 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH24 : (retval = 1)) (PreH25 : (out_pre = x_pre)) (PreH26 : ((-INT_MAX) <= A_r_eq_x)) (PreH27 : (A_r_eq_x <= INT_MAX)) (PreH28 : ((-INT_MAX) <= C_r_eq_x)) (PreH29 : (C_r_eq_x <= INT_MAX)) (PreH30 : (1 <= B_r_eq_x)) (PreH31 : (B_r_eq_x <= INT_MAX)) (PreH32 : (1 <= E_r_eq_x)) (PreH33 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((-INT_MAX) <= ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )) ”
).

Definition rat_add_partial_solve_wit_17_r_eq_x_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (E_r_eq_x <= INT_MAX)) (PreH2 : (C_r_eq_x <= INT_MAX)) (PreH3 : ((A_r_eq_x * E_r_eq_x ) <= INT_MAX)) (PreH4 : ((C_r_eq_x * B_r_eq_x ) <= INT_MAX)) (PreH5 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <= INT_MAX)) (PreH6 : ((B_r_eq_x * E_r_eq_x ) <= INT_MAX)) (PreH7 : (E_r_eq_x >= INT_MIN)) (PreH8 : (C_r_eq_x >= INT_MIN)) (PreH9 : ((A_r_eq_x * E_r_eq_x ) >= INT_MIN)) (PreH10 : ((C_r_eq_x * B_r_eq_x ) >= INT_MIN)) (PreH11 : (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) >= INT_MIN)) (PreH12 : ((B_r_eq_x * E_r_eq_x ) >= INT_MIN)) (PreH13 : (retval_4 <> 0)) (PreH14 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH15 : (retval_4 = 1)) (PreH16 : (retval_3 <> 0)) (PreH17 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH18 : (retval_3 = 1)) (PreH19 : (retval_2 <> 0)) (PreH20 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH21 : (retval_2 = 1)) (PreH22 : (retval <> 0)) (PreH23 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH24 : (retval = 1)) (PreH25 : (out_pre = x_pre)) (PreH26 : ((-INT_MAX) <= A_r_eq_x)) (PreH27 : (A_r_eq_x <= INT_MAX)) (PreH28 : ((-INT_MAX) <= C_r_eq_x)) (PreH29 : (C_r_eq_x <= INT_MAX)) (PreH30 : (1 <= B_r_eq_x)) (PreH31 : (B_r_eq_x <= INT_MAX)) (PreH32 : (1 <= E_r_eq_x)) (PreH33 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "d" ) )) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((( &( "n" ) )) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((( &( "q" ) )) # Int  |-> (C_r_eq_x * B_r_eq_x ))
  **  ((( &( "p" ) )) # Int  |-> (A_r_eq_x * E_r_eq_x ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ ((-INT_MAX) <= ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )) ”
.

Definition rat_add_partial_solve_wit_17_r_eq_x_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (E_r_eq_x: Z) (C_r_eq_x: Z) (B_r_eq_x: Z) (A_r_eq_x: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x)))) (PreH3 : (retval_4 = 1)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x ))))) (PreH6 : (retval_3 = 1)) (PreH7 : (retval_2 <> 0)) (PreH8 : (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x)))) (PreH9 : (retval_2 = 1)) (PreH10 : (retval <> 0)) (PreH11 : (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x)))) (PreH12 : (retval = 1)) (PreH13 : (out_pre = x_pre)) (PreH14 : ((-INT_MAX) <= A_r_eq_x)) (PreH15 : (A_r_eq_x <= INT_MAX)) (PreH16 : ((-INT_MAX) <= C_r_eq_x)) (PreH17 : (C_r_eq_x <= INT_MAX)) (PreH18 : (1 <= B_r_eq_x)) (PreH19 : (B_r_eq_x <= INT_MAX)) (PreH20 : (1 <= E_r_eq_x)) (PreH21 : (E_r_eq_x <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
|--
  “ (1 <= (B_r_eq_x * E_r_eq_x )) ” 
  &&  “ ((B_r_eq_x * E_r_eq_x ) <= INT_MAX) ” 
  &&  “ (((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) )) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_4 = (checked_mul_flag (B_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval_4 = 1) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (checked_add_flag ((A_r_eq_x * E_r_eq_x )) ((C_r_eq_x * B_r_eq_x )))) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (C_r_eq_x) (B_r_eq_x))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_r_eq_x) (E_r_eq_x))) ” 
  &&  “ (retval = 1) ” 
  &&  “ (out_pre = x_pre) ” 
  &&  “ ((-INT_MAX) <= A_r_eq_x) ” 
  &&  “ (A_r_eq_x <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= C_r_eq_x) ” 
  &&  “ (C_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= B_r_eq_x) ” 
  &&  “ (B_r_eq_x <= INT_MAX) ” 
  &&  “ (1 <= E_r_eq_x) ” 
  &&  “ (E_r_eq_x <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> ((A_r_eq_x * E_r_eq_x ) + (C_r_eq_x * B_r_eq_x ) ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_r_eq_x * E_r_eq_x ))
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_r_eq_x)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> E_r_eq_x)
.

Definition rat_add_partial_solve_wit_17_r_eq_x := rat_add_partial_solve_wit_17_r_eq_x_pure -> rat_add_partial_solve_wit_17_r_eq_x_aux.

Module Type VC_Correct.


Axiom proof_of_rat_add_safety_wit_1_out_known : rat_add_safety_wit_1_out_known.
Axiom proof_of_rat_add_safety_wit_2_out_known : rat_add_safety_wit_2_out_known.
Axiom proof_of_rat_add_safety_wit_3_out_undef : rat_add_safety_wit_3_out_undef.
Axiom proof_of_rat_add_safety_wit_4_out_undef : rat_add_safety_wit_4_out_undef.
Axiom proof_of_rat_add_safety_wit_5_r_eq_x : rat_add_safety_wit_5_r_eq_x.
Axiom proof_of_rat_add_safety_wit_6_r_eq_x : rat_add_safety_wit_6_r_eq_x.
Axiom proof_of_rat_add_safety_wit_7_out_known : rat_add_safety_wit_7_out_known.
Axiom proof_of_rat_add_safety_wit_8_out_undef : rat_add_safety_wit_8_out_undef.
Axiom proof_of_rat_add_safety_wit_9_r_eq_x : rat_add_safety_wit_9_r_eq_x.
Axiom proof_of_rat_add_safety_wit_10_out_known : rat_add_safety_wit_10_out_known.
Axiom proof_of_rat_add_safety_wit_11_out_known : rat_add_safety_wit_11_out_known.
Axiom proof_of_rat_add_safety_wit_12_out_undef : rat_add_safety_wit_12_out_undef.
Axiom proof_of_rat_add_safety_wit_13_out_undef : rat_add_safety_wit_13_out_undef.
Axiom proof_of_rat_add_safety_wit_14_r_eq_x : rat_add_safety_wit_14_r_eq_x.
Axiom proof_of_rat_add_safety_wit_15_r_eq_x : rat_add_safety_wit_15_r_eq_x.
Axiom proof_of_rat_add_safety_wit_16_out_known : rat_add_safety_wit_16_out_known.
Axiom proof_of_rat_add_safety_wit_17_out_undef : rat_add_safety_wit_17_out_undef.
Axiom proof_of_rat_add_safety_wit_18_r_eq_x : rat_add_safety_wit_18_r_eq_x.
Axiom proof_of_rat_add_safety_wit_19_out_known : rat_add_safety_wit_19_out_known.
Axiom proof_of_rat_add_safety_wit_20_out_known : rat_add_safety_wit_20_out_known.
Axiom proof_of_rat_add_safety_wit_21_out_undef : rat_add_safety_wit_21_out_undef.
Axiom proof_of_rat_add_safety_wit_22_out_undef : rat_add_safety_wit_22_out_undef.
Axiom proof_of_rat_add_safety_wit_23_r_eq_x : rat_add_safety_wit_23_r_eq_x.
Axiom proof_of_rat_add_safety_wit_24_r_eq_x : rat_add_safety_wit_24_r_eq_x.
Axiom proof_of_rat_add_safety_wit_25_out_known : rat_add_safety_wit_25_out_known.
Axiom proof_of_rat_add_safety_wit_26_out_undef : rat_add_safety_wit_26_out_undef.
Axiom proof_of_rat_add_safety_wit_27_r_eq_x : rat_add_safety_wit_27_r_eq_x.
Axiom proof_of_rat_add_safety_wit_28_out_known : rat_add_safety_wit_28_out_known.
Axiom proof_of_rat_add_safety_wit_29_out_known : rat_add_safety_wit_29_out_known.
Axiom proof_of_rat_add_safety_wit_30_out_undef : rat_add_safety_wit_30_out_undef.
Axiom proof_of_rat_add_safety_wit_31_out_undef : rat_add_safety_wit_31_out_undef.
Axiom proof_of_rat_add_safety_wit_32_r_eq_x : rat_add_safety_wit_32_r_eq_x.
Axiom proof_of_rat_add_safety_wit_33_r_eq_x : rat_add_safety_wit_33_r_eq_x.
Axiom proof_of_rat_add_safety_wit_34_out_known : rat_add_safety_wit_34_out_known.
Axiom proof_of_rat_add_safety_wit_35_out_undef : rat_add_safety_wit_35_out_undef.
Axiom proof_of_rat_add_safety_wit_36_r_eq_x : rat_add_safety_wit_36_r_eq_x.
Axiom proof_of_rat_add_safety_wit_37_out_known : rat_add_safety_wit_37_out_known.
Axiom proof_of_rat_add_safety_wit_38_out_known : rat_add_safety_wit_38_out_known.
Axiom proof_of_rat_add_safety_wit_39_out_known : rat_add_safety_wit_39_out_known.
Axiom proof_of_rat_add_safety_wit_40_out_known : rat_add_safety_wit_40_out_known.
Axiom proof_of_rat_add_safety_wit_41_out_undef : rat_add_safety_wit_41_out_undef.
Axiom proof_of_rat_add_safety_wit_42_out_undef : rat_add_safety_wit_42_out_undef.
Axiom proof_of_rat_add_safety_wit_43_out_undef : rat_add_safety_wit_43_out_undef.
Axiom proof_of_rat_add_safety_wit_44_out_undef : rat_add_safety_wit_44_out_undef.
Axiom proof_of_rat_add_safety_wit_45_r_eq_x : rat_add_safety_wit_45_r_eq_x.
Axiom proof_of_rat_add_safety_wit_46_r_eq_x : rat_add_safety_wit_46_r_eq_x.
Axiom proof_of_rat_add_safety_wit_47_r_eq_x : rat_add_safety_wit_47_r_eq_x.
Axiom proof_of_rat_add_safety_wit_48_r_eq_x : rat_add_safety_wit_48_r_eq_x.
Axiom proof_of_rat_add_return_wit_1_out_known : rat_add_return_wit_1_out_known.
Axiom proof_of_rat_add_return_wit_2_out_known : rat_add_return_wit_2_out_known.
Axiom proof_of_rat_add_return_wit_3_out_known : rat_add_return_wit_3_out_known.
Axiom proof_of_rat_add_return_wit_4_out_known : rat_add_return_wit_4_out_known.
Axiom proof_of_rat_add_return_wit_5_out_undef : rat_add_return_wit_5_out_undef.
Axiom proof_of_rat_add_return_wit_6_out_undef : rat_add_return_wit_6_out_undef.
Axiom proof_of_rat_add_return_wit_7_out_undef : rat_add_return_wit_7_out_undef.
Axiom proof_of_rat_add_return_wit_8_out_undef : rat_add_return_wit_8_out_undef.
Axiom proof_of_rat_add_return_wit_9_r_eq_x : rat_add_return_wit_9_r_eq_x.
Axiom proof_of_rat_add_return_wit_10_r_eq_x : rat_add_return_wit_10_r_eq_x.
Axiom proof_of_rat_add_return_wit_11_r_eq_x : rat_add_return_wit_11_r_eq_x.
Axiom proof_of_rat_add_return_wit_12_r_eq_x : rat_add_return_wit_12_r_eq_x.
Axiom proof_of_rat_add_return_wit_13_out_known : rat_add_return_wit_13_out_known.
Axiom proof_of_rat_add_return_wit_14_out_undef : rat_add_return_wit_14_out_undef.
Axiom proof_of_rat_add_return_wit_15_r_eq_x : rat_add_return_wit_15_r_eq_x.
Axiom proof_of_rat_add_return_wit_16_out_known : rat_add_return_wit_16_out_known.
Axiom proof_of_rat_add_return_wit_17_out_undef : rat_add_return_wit_17_out_undef.
Axiom proof_of_rat_add_return_wit_18_r_eq_x : rat_add_return_wit_18_r_eq_x.
Axiom proof_of_rat_add_return_wit_19_out_known : rat_add_return_wit_19_out_known.
Axiom proof_of_rat_add_return_wit_20_out_undef : rat_add_return_wit_20_out_undef.
Axiom proof_of_rat_add_return_wit_21_r_eq_x : rat_add_return_wit_21_r_eq_x.
Axiom proof_of_rat_add_return_wit_22_out_known : rat_add_return_wit_22_out_known.
Axiom proof_of_rat_add_return_wit_23_out_undef : rat_add_return_wit_23_out_undef.
Axiom proof_of_rat_add_return_wit_24_r_eq_x : rat_add_return_wit_24_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_1_out_known_pure : rat_add_partial_solve_wit_1_out_known_pure.
Axiom proof_of_rat_add_partial_solve_wit_1_out_known : rat_add_partial_solve_wit_1_out_known.
Axiom proof_of_rat_add_partial_solve_wit_2_out_undef_pure : rat_add_partial_solve_wit_2_out_undef_pure.
Axiom proof_of_rat_add_partial_solve_wit_2_out_undef : rat_add_partial_solve_wit_2_out_undef.
Axiom proof_of_rat_add_partial_solve_wit_3_r_eq_x_pure : rat_add_partial_solve_wit_3_r_eq_x_pure.
Axiom proof_of_rat_add_partial_solve_wit_3_r_eq_x : rat_add_partial_solve_wit_3_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_4_out_known_pure : rat_add_partial_solve_wit_4_out_known_pure.
Axiom proof_of_rat_add_partial_solve_wit_4_out_known : rat_add_partial_solve_wit_4_out_known.
Axiom proof_of_rat_add_partial_solve_wit_5_out_undef_pure : rat_add_partial_solve_wit_5_out_undef_pure.
Axiom proof_of_rat_add_partial_solve_wit_5_out_undef : rat_add_partial_solve_wit_5_out_undef.
Axiom proof_of_rat_add_partial_solve_wit_6_r_eq_x_pure : rat_add_partial_solve_wit_6_r_eq_x_pure.
Axiom proof_of_rat_add_partial_solve_wit_6_r_eq_x : rat_add_partial_solve_wit_6_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_7_out_known_pure : rat_add_partial_solve_wit_7_out_known_pure.
Axiom proof_of_rat_add_partial_solve_wit_7_out_known : rat_add_partial_solve_wit_7_out_known.
Axiom proof_of_rat_add_partial_solve_wit_8_out_undef_pure : rat_add_partial_solve_wit_8_out_undef_pure.
Axiom proof_of_rat_add_partial_solve_wit_8_out_undef : rat_add_partial_solve_wit_8_out_undef.
Axiom proof_of_rat_add_partial_solve_wit_9_r_eq_x_pure : rat_add_partial_solve_wit_9_r_eq_x_pure.
Axiom proof_of_rat_add_partial_solve_wit_9_r_eq_x : rat_add_partial_solve_wit_9_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_10_out_known_pure : rat_add_partial_solve_wit_10_out_known_pure.
Axiom proof_of_rat_add_partial_solve_wit_10_out_known : rat_add_partial_solve_wit_10_out_known.
Axiom proof_of_rat_add_partial_solve_wit_11_out_undef_pure : rat_add_partial_solve_wit_11_out_undef_pure.
Axiom proof_of_rat_add_partial_solve_wit_11_out_undef : rat_add_partial_solve_wit_11_out_undef.
Axiom proof_of_rat_add_partial_solve_wit_12_r_eq_x_pure : rat_add_partial_solve_wit_12_r_eq_x_pure.
Axiom proof_of_rat_add_partial_solve_wit_12_r_eq_x : rat_add_partial_solve_wit_12_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_13_r_eq_x : rat_add_partial_solve_wit_13_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_14_r_eq_x : rat_add_partial_solve_wit_14_r_eq_x.
Axiom proof_of_rat_add_partial_solve_wit_15_out_known_pure : rat_add_partial_solve_wit_15_out_known_pure.
Axiom proof_of_rat_add_partial_solve_wit_15_out_known : rat_add_partial_solve_wit_15_out_known.
Axiom proof_of_rat_add_partial_solve_wit_16_out_undef_pure : rat_add_partial_solve_wit_16_out_undef_pure.
Axiom proof_of_rat_add_partial_solve_wit_16_out_undef : rat_add_partial_solve_wit_16_out_undef.
Axiom proof_of_rat_add_partial_solve_wit_17_r_eq_x_pure : rat_add_partial_solve_wit_17_r_eq_x_pure.
Axiom proof_of_rat_add_partial_solve_wit_17_r_eq_x : rat_add_partial_solve_wit_17_r_eq_x.

End VC_Correct.
