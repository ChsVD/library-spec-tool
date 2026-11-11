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
Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib.
Local Open Scope sac.

(*----- Function rat_mul -----*)

Definition rat_mul_safety_wit_1_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_mul_safety_wit_2_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_mul_safety_wit_3_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_mul_safety_wit_4_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_mul_safety_wit_5_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_mul_safety_wit_6_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_mul_safety_wit_7_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_mul_safety_wit_8_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ False ”
.

Definition rat_mul_safety_wit_9_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_mul_safety_wit_10_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition rat_mul_safety_wit_11_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_mul_safety_wit_12_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_mul_safety_wit_13_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_14_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (A_out_known * C_out_known ))) (PreH11 : (Q = (B_out_known * D_out_known ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= D_out_known)) (PreH25 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_15_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_known)) (PreH17 : (A_out_known <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_known)) (PreH19 : (C_out_known <= INT_MAX)) (PreH20 : (1 <= B_out_known)) (PreH21 : (B_out_known <= INT_MAX)) (PreH22 : (1 <= D_out_known)) (PreH23 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_16_out_known := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : (P = (A_out_known * C_out_known ))) (PreH10 : (Q = (B_out_known * D_out_known ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_17_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_18_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) ))) (PreH8 : (P = 0)) (PreH9 : (Q = 1)) (PreH10 : (P = (A_out_undef * C_out_undef ))) (PreH11 : (Q = (B_out_undef * D_out_undef ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= D_out_undef)) (PreH25 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_19_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_undef)) (PreH17 : (A_out_undef <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_undef)) (PreH19 : (C_out_undef <= INT_MAX)) (PreH20 : (1 <= B_out_undef)) (PreH21 : (B_out_undef <= INT_MAX)) (PreH22 : (1 <= D_out_undef)) (PreH23 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_safety_wit_20_out_undef := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P: Z) (Q: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P Q )) (PreH2 : ((-INT_MAX) <= P)) (PreH3 : (P <= INT_MAX)) (PreH4 : (1 <= Q)) (PreH5 : (Q <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : (P = (A_out_undef * C_out_undef ))) (PreH10 : (Q = (B_out_undef * D_out_undef ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
  **  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_mul_return_wit_1_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_mul_return_wit_1_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_mul_return_wit_1_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known 0 1 )
.

Definition rat_mul_return_wit_1_out_known_split_goal_3 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_mul_return_wit_2_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * C_out_known ))) (PreH11 : (Q_2 = (B_out_known * D_out_known ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= D_out_known)) (PreH25 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * C_out_known ))) (PreH11 : (Q_2 = (B_out_known * D_out_known ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= D_out_known)) (PreH25 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known 0 1 ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_mul_return_wit_2_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * C_out_known ))) (PreH11 : (Q_2 = (B_out_known * D_out_known ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= D_out_known)) (PreH25 : (D_out_known <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_mul_return_wit_2_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * C_out_known ))) (PreH11 : (Q_2 = (B_out_known * D_out_known ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= D_out_known)) (PreH25 : (D_out_known <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known 0 1 )
.

Definition rat_mul_return_wit_2_out_known_split_goal_3 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_known * C_out_known ))) (PreH11 : (Q_2 = (B_out_known * D_out_known ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_known)) (PreH19 : (A_out_known <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_known)) (PreH21 : (C_out_known <= INT_MAX)) (PreH22 : (1 <= B_out_known)) (PreH23 : (B_out_known <= INT_MAX)) (PreH24 : (1 <= D_out_known)) (PreH25 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_mul_return_wit_3_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_known)) (PreH17 : (A_out_known <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_known)) (PreH19 : (C_out_known <= INT_MAX)) (PreH20 : (1 <= B_out_known)) (PreH21 : (B_out_known <= INT_MAX)) (PreH22 : (1 <= D_out_known)) (PreH23 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) )) ” 
  &&  “ ((A_out_known * C_out_known ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_known)) (PreH17 : (A_out_known <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_known)) (PreH19 : (C_out_known <= INT_MAX)) (PreH20 : (1 <= B_out_known)) (PreH21 : (B_out_known <= INT_MAX)) (PreH22 : (1 <= D_out_known)) (PreH23 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_mul_return_wit_3_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_known)) (PreH17 : (A_out_known <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_known)) (PreH19 : (C_out_known <= INT_MAX)) (PreH20 : (1 <= B_out_known)) (PreH21 : (B_out_known <= INT_MAX)) (PreH22 : (1 <= D_out_known)) (PreH23 : (D_out_known <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known P_2 Q_2 )
.

Definition rat_mul_return_wit_3_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_known * C_out_known )))) ((B_out_known * D_out_known ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_known)) (PreH17 : (A_out_known <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_known)) (PreH19 : (C_out_known <= INT_MAX)) (PreH20 : (1 <= B_out_known)) (PreH21 : (B_out_known <= INT_MAX)) (PreH22 : (1 <= D_out_known)) (PreH23 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_mul_return_wit_4_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * C_out_known ))) (PreH10 : (Q_2 = (B_out_known * D_out_known ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_known * C_out_known ) * Q ) = (P * (B_out_known * D_out_known ) )) ” 
  &&  “ ((A_out_known * C_out_known ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * C_out_known ))) (PreH10 : (Q_2 = (B_out_known * D_out_known ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known (A_out_known * C_out_known ) (B_out_known * D_out_known ) ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_mul_return_wit_4_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * C_out_known ))) (PreH10 : (Q_2 = (B_out_known * D_out_known ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_known B_out_known C_out_known D_out_known (A_out_known * C_out_known ) (B_out_known * D_out_known ) )
.

Definition rat_mul_return_wit_4_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_known * C_out_known ) (B_out_known * D_out_known ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_known * C_out_known ) * Q_2 ) = (P_2 * (B_out_known * D_out_known ) ))) (PreH8 : ((A_out_known * C_out_known ) <> 0)) (PreH9 : (P_2 = (A_out_known * C_out_known ))) (PreH10 : (Q_2 = (B_out_known * D_out_known ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_known)) (PreH18 : (A_out_known <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_known)) (PreH20 : (C_out_known <= INT_MAX)) (PreH21 : (1 <= B_out_known)) (PreH22 : (B_out_known <= INT_MAX)) (PreH23 : (1 <= D_out_known)) (PreH24 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_mul_return_wit_5_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_mul_return_wit_5_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_mul_return_wit_5_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef 0 1 )
.

Definition rat_mul_return_wit_5_out_undef_split_goal_3 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_mul_return_wit_6_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * C_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= D_out_undef)) (PreH25 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * C_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= D_out_undef)) (PreH25 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Zgcd ((Zabs (0))) (1)) = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef 0 1 ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_mul_return_wit_6_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * C_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= D_out_undef)) (PreH25 : (D_out_undef <= INT_MAX)) ,
  ((Zgcd ((Zabs (0))) (1)) = 1)
.

Definition rat_mul_return_wit_6_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * C_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= D_out_undef)) (PreH25 : (D_out_undef <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef 0 1 )
.

Definition rat_mul_return_wit_6_out_undef_split_goal_3 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : (P_2 = 0)) (PreH9 : (Q_2 = 1)) (PreH10 : (P_2 = (A_out_undef * C_out_undef ))) (PreH11 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH12 : (retval_2 <> 0)) (PreH13 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH14 : (retval_2 = 1)) (PreH15 : (retval <> 0)) (PreH16 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH17 : (retval = 1)) (PreH18 : ((INT_MIN) <= A_out_undef)) (PreH19 : (A_out_undef <= INT_MAX)) (PreH20 : ((INT_MIN) <= C_out_undef)) (PreH21 : (C_out_undef <= INT_MAX)) (PreH22 : (1 <= B_out_undef)) (PreH23 : (B_out_undef <= INT_MAX)) (PreH24 : (1 <= D_out_undef)) (PreH25 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_mul_return_wit_7_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_undef)) (PreH17 : (A_out_undef <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_undef)) (PreH19 : (C_out_undef <= INT_MAX)) (PreH20 : (1 <= B_out_undef)) (PreH21 : (B_out_undef <= INT_MAX)) (PreH22 : (1 <= D_out_undef)) (PreH23 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) )) ” 
  &&  “ ((A_out_undef * C_out_undef ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_undef)) (PreH17 : (A_out_undef <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_undef)) (PreH19 : (C_out_undef <= INT_MAX)) (PreH20 : (1 <= B_out_undef)) (PreH21 : (B_out_undef <= INT_MAX)) (PreH22 : (1 <= D_out_undef)) (PreH23 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef P_2 Q_2 ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_mul_return_wit_7_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_undef)) (PreH17 : (A_out_undef <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_undef)) (PreH19 : (C_out_undef <= INT_MAX)) (PreH20 : (1 <= B_out_undef)) (PreH21 : (B_out_undef <= INT_MAX)) (PreH22 : (1 <= D_out_undef)) (PreH23 : (D_out_undef <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef P_2 Q_2 )
.

Definition rat_mul_return_wit_7_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : ((Zgcd ((Zabs ((A_out_undef * C_out_undef )))) ((B_out_undef * D_out_undef ))) <> 1)) (PreH10 : (retval_2 <> 0)) (PreH11 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH12 : (retval_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH15 : (retval = 1)) (PreH16 : ((INT_MIN) <= A_out_undef)) (PreH17 : (A_out_undef <= INT_MAX)) (PreH18 : ((INT_MIN) <= C_out_undef)) (PreH19 : (C_out_undef <= INT_MAX)) (PreH20 : (1 <= B_out_undef)) (PreH21 : (B_out_undef <= INT_MAX)) (PreH22 : (1 <= D_out_undef)) (PreH23 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_mul_return_wit_8_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * C_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P_2)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q_2)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
|--
  EX (P: Z)  (Q: Z) ,
  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ” 
  &&  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ (((A_out_undef * C_out_undef ) * Q ) = (P * (B_out_undef * D_out_undef ) )) ” 
  &&  “ ((A_out_undef * C_out_undef ) <> 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * C_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) ) ” 
  &&  “ (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_mul_return_wit_8_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * C_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  (simplex_rat_mul_result A_out_undef B_out_undef C_out_undef D_out_undef (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) )
.

Definition rat_mul_return_wit_8_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (P_2: Z) (Q_2: Z) (PreH1 : (simplex_rat_reduce_result (A_out_undef * C_out_undef ) (B_out_undef * D_out_undef ) P_2 Q_2 )) (PreH2 : ((-INT_MAX) <= P_2)) (PreH3 : (P_2 <= INT_MAX)) (PreH4 : (1 <= Q_2)) (PreH5 : (Q_2 <= INT_MAX)) (PreH6 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH7 : (((A_out_undef * C_out_undef ) * Q_2 ) = (P_2 * (B_out_undef * D_out_undef ) ))) (PreH8 : ((A_out_undef * C_out_undef ) <> 0)) (PreH9 : (P_2 = (A_out_undef * C_out_undef ))) (PreH10 : (Q_2 = (B_out_undef * D_out_undef ))) (PreH11 : (retval_2 <> 0)) (PreH12 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH13 : (retval_2 = 1)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH16 : (retval = 1)) (PreH17 : ((INT_MIN) <= A_out_undef)) (PreH18 : (A_out_undef <= INT_MAX)) (PreH19 : ((INT_MIN) <= C_out_undef)) (PreH20 : (C_out_undef <= INT_MAX)) (PreH21 : (1 <= B_out_undef)) (PreH22 : (B_out_undef <= INT_MAX)) (PreH23 : (1 <= D_out_undef)) (PreH24 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_mul_return_wit_9_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_mul_return_wit_9_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_mul_return_wit_10_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_mul_return_wit_10_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_mul_return_wit_11_out_known := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (0 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_mul_return_wit_11_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_mul_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_mul_return_wit_12_out_undef := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (0 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_mul_return_wit_12_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_mul_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_mul_partial_solve_wit_1_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((INT_MIN) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= D_out_known)) (PreH8 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (A_out_known = A_out_known) ” 
  &&  “ (C_out_known = C_out_known) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ”
.

Definition rat_mul_partial_solve_wit_1_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((INT_MIN) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= D_out_known)) (PreH8 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (A_out_known = A_out_known) ” 
  &&  “ (C_out_known = C_out_known) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
.

Definition rat_mul_partial_solve_wit_1_out_known := rat_mul_partial_solve_wit_1_out_known_pure -> rat_mul_partial_solve_wit_1_out_known_aux.

Definition rat_mul_partial_solve_wit_2_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((INT_MIN) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= D_out_undef)) (PreH8 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (A_out_undef = A_out_undef) ” 
  &&  “ (C_out_undef = C_out_undef) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ”
.

Definition rat_mul_partial_solve_wit_2_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((INT_MIN) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= D_out_undef)) (PreH8 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (A_out_undef = A_out_undef) ” 
  &&  “ (C_out_undef = C_out_undef) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
.

Definition rat_mul_partial_solve_wit_2_out_undef := rat_mul_partial_solve_wit_2_out_undef_pure -> rat_mul_partial_solve_wit_2_out_undef_aux.

Definition rat_mul_partial_solve_wit_3_out_known_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (B_out_known = B_out_known) ” 
  &&  “ (D_out_known = D_out_known) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ”
.

Definition rat_mul_partial_solve_wit_3_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (oldd_out_known: Z) (oldn_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
|--
  “ (B_out_known = B_out_known) ” 
  &&  “ (D_out_known = D_out_known) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (C_out_known))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> oldn_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> oldd_out_known)
.

Definition rat_mul_partial_solve_wit_3_out_known := rat_mul_partial_solve_wit_3_out_known_pure -> rat_mul_partial_solve_wit_3_out_known_aux.

Definition rat_mul_partial_solve_wit_4_out_undef_pure := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (B_out_undef = B_out_undef) ” 
  &&  “ (D_out_undef = D_out_undef) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ”
.

Definition rat_mul_partial_solve_wit_4_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (B_out_undef = B_out_undef) ” 
  &&  “ (D_out_undef = D_out_undef) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (C_out_undef))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |->_)
.

Definition rat_mul_partial_solve_wit_4_out_undef := rat_mul_partial_solve_wit_4_out_undef_pure -> rat_mul_partial_solve_wit_4_out_undef_aux.

Definition rat_mul_partial_solve_wit_5_out_known_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * C_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * D_out_known ))
|--
  “ (1 <= (B_out_known * D_out_known )) ” 
  &&  “ ((B_out_known * D_out_known ) <= INT_MAX) ” 
  &&  “ ((A_out_known * C_out_known ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_known * C_out_known )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (D_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((A_out_known * C_out_known ) <= INT_MAX)) (PreH6 : ((B_out_known * D_out_known ) <= INT_MAX)) (PreH7 : (D_out_known >= INT_MIN)) (PreH8 : (C_out_known >= INT_MIN)) (PreH9 : (B_out_known >= INT_MIN)) (PreH10 : (A_out_known >= INT_MIN)) (PreH11 : ((A_out_known * C_out_known ) >= INT_MIN)) (PreH12 : ((B_out_known * D_out_known ) >= INT_MIN)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH18 : (retval = 1)) (PreH19 : ((INT_MIN) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((INT_MIN) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= D_out_known)) (PreH26 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * C_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * D_out_known ))
|--
  “ ((-INT_MAX) <= (A_out_known * C_out_known )) ”
).

Definition rat_mul_partial_solve_wit_5_out_known_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (D_out_known <= INT_MAX)) (PreH2 : (C_out_known <= INT_MAX)) (PreH3 : (B_out_known <= INT_MAX)) (PreH4 : (A_out_known <= INT_MAX)) (PreH5 : ((A_out_known * C_out_known ) <= INT_MAX)) (PreH6 : ((B_out_known * D_out_known ) <= INT_MAX)) (PreH7 : (D_out_known >= INT_MIN)) (PreH8 : (C_out_known >= INT_MIN)) (PreH9 : (B_out_known >= INT_MIN)) (PreH10 : (A_out_known >= INT_MIN)) (PreH11 : ((A_out_known * C_out_known ) >= INT_MIN)) (PreH12 : ((B_out_known * D_out_known ) >= INT_MIN)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH18 : (retval = 1)) (PreH19 : ((INT_MIN) <= A_out_known)) (PreH20 : (A_out_known <= INT_MAX)) (PreH21 : ((INT_MIN) <= C_out_known)) (PreH22 : (C_out_known <= INT_MAX)) (PreH23 : (1 <= B_out_known)) (PreH24 : (B_out_known <= INT_MAX)) (PreH25 : (1 <= D_out_known)) (PreH26 : (D_out_known <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_known * D_out_known ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_known * C_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * C_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * D_out_known ))
|--
  “ ((-INT_MAX) <= (A_out_known * C_out_known )) ”
.

Definition rat_mul_partial_solve_wit_5_out_known_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_known) (D_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (C_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * C_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * D_out_known ))
|--
  “ (1 <= (B_out_known * D_out_known )) ” 
  &&  “ ((B_out_known * D_out_known ) <= INT_MAX) ” 
  &&  “ ((A_out_known * C_out_known ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_known * C_out_known )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_out_known) (D_out_known))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (C_out_known))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ (1 <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (1 <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_known * C_out_known ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_known * D_out_known ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
.

Definition rat_mul_partial_solve_wit_5_out_known := rat_mul_partial_solve_wit_5_out_known_pure -> rat_mul_partial_solve_wit_5_out_known_aux.

Definition rat_mul_partial_solve_wit_6_out_undef_pure := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * D_out_undef ))
|--
  “ (1 <= (B_out_undef * D_out_undef )) ” 
  &&  “ ((B_out_undef * D_out_undef ) <= INT_MAX) ” 
  &&  “ ((A_out_undef * C_out_undef ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_undef * C_out_undef )) ”
) \/
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (D_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((A_out_undef * C_out_undef ) <= INT_MAX)) (PreH6 : ((B_out_undef * D_out_undef ) <= INT_MAX)) (PreH7 : (D_out_undef >= INT_MIN)) (PreH8 : (C_out_undef >= INT_MIN)) (PreH9 : (B_out_undef >= INT_MIN)) (PreH10 : (A_out_undef >= INT_MIN)) (PreH11 : ((A_out_undef * C_out_undef ) >= INT_MIN)) (PreH12 : ((B_out_undef * D_out_undef ) >= INT_MIN)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : ((INT_MIN) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((INT_MIN) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= D_out_undef)) (PreH26 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * D_out_undef ))
|--
  “ ((-INT_MAX) <= (A_out_undef * C_out_undef )) ”
).

Definition rat_mul_partial_solve_wit_6_out_undef_pure_split_goal_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (D_out_undef <= INT_MAX)) (PreH2 : (C_out_undef <= INT_MAX)) (PreH3 : (B_out_undef <= INT_MAX)) (PreH4 : (A_out_undef <= INT_MAX)) (PreH5 : ((A_out_undef * C_out_undef ) <= INT_MAX)) (PreH6 : ((B_out_undef * D_out_undef ) <= INT_MAX)) (PreH7 : (D_out_undef >= INT_MIN)) (PreH8 : (C_out_undef >= INT_MIN)) (PreH9 : (B_out_undef >= INT_MIN)) (PreH10 : (A_out_undef >= INT_MIN)) (PreH11 : ((A_out_undef * C_out_undef ) >= INT_MIN)) (PreH12 : ((B_out_undef * D_out_undef ) >= INT_MIN)) (PreH13 : (retval_2 <> 0)) (PreH14 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH15 : (retval_2 = 1)) (PreH16 : (retval <> 0)) (PreH17 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH18 : (retval = 1)) (PreH19 : ((INT_MIN) <= A_out_undef)) (PreH20 : (A_out_undef <= INT_MAX)) (PreH21 : ((INT_MIN) <= C_out_undef)) (PreH22 : (C_out_undef <= INT_MAX)) (PreH23 : (1 <= B_out_undef)) (PreH24 : (B_out_undef <= INT_MAX)) (PreH25 : (1 <= D_out_undef)) (PreH26 : (D_out_undef <= INT_MAX)) ,
  ((( &( "d" ) )) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((( &( "n" ) )) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * D_out_undef ))
|--
  “ ((-INT_MAX) <= (A_out_undef * C_out_undef )) ”
.

Definition rat_mul_partial_solve_wit_6_out_undef_aux := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (C_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * D_out_undef ))
|--
  “ (1 <= (B_out_undef * D_out_undef )) ” 
  &&  “ ((B_out_undef * D_out_undef ) <= INT_MAX) ” 
  &&  “ ((A_out_undef * C_out_undef ) <= INT_MAX) ” 
  &&  “ ((-INT_MAX) <= (A_out_undef * C_out_undef )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (checked_mul_flag (B_out_undef) (D_out_undef))) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (C_out_undef))) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ (1 <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (1 <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ”
  &&  ((&((out_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (A_out_undef * C_out_undef ))
  **  ((&((out_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (B_out_undef * D_out_undef ))
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
.

Definition rat_mul_partial_solve_wit_6_out_undef := rat_mul_partial_solve_wit_6_out_undef_pure -> rat_mul_partial_solve_wit_6_out_undef_aux.

Module Type VC_Correct.


Axiom proof_of_rat_mul_safety_wit_1_out_known : rat_mul_safety_wit_1_out_known.
Axiom proof_of_rat_mul_safety_wit_2_out_known : rat_mul_safety_wit_2_out_known.
Axiom proof_of_rat_mul_safety_wit_3_out_undef : rat_mul_safety_wit_3_out_undef.
Axiom proof_of_rat_mul_safety_wit_4_out_undef : rat_mul_safety_wit_4_out_undef.
Axiom proof_of_rat_mul_safety_wit_5_out_known : rat_mul_safety_wit_5_out_known.
Axiom proof_of_rat_mul_safety_wit_6_out_undef : rat_mul_safety_wit_6_out_undef.
Axiom proof_of_rat_mul_safety_wit_7_out_known : rat_mul_safety_wit_7_out_known.
Axiom proof_of_rat_mul_safety_wit_8_out_known : rat_mul_safety_wit_8_out_known.
Axiom proof_of_rat_mul_safety_wit_9_out_undef : rat_mul_safety_wit_9_out_undef.
Axiom proof_of_rat_mul_safety_wit_10_out_undef : rat_mul_safety_wit_10_out_undef.
Axiom proof_of_rat_mul_safety_wit_11_out_known : rat_mul_safety_wit_11_out_known.
Axiom proof_of_rat_mul_safety_wit_12_out_undef : rat_mul_safety_wit_12_out_undef.
Axiom proof_of_rat_mul_safety_wit_13_out_known : rat_mul_safety_wit_13_out_known.
Axiom proof_of_rat_mul_safety_wit_14_out_known : rat_mul_safety_wit_14_out_known.
Axiom proof_of_rat_mul_safety_wit_15_out_known : rat_mul_safety_wit_15_out_known.
Axiom proof_of_rat_mul_safety_wit_16_out_known : rat_mul_safety_wit_16_out_known.
Axiom proof_of_rat_mul_safety_wit_17_out_undef : rat_mul_safety_wit_17_out_undef.
Axiom proof_of_rat_mul_safety_wit_18_out_undef : rat_mul_safety_wit_18_out_undef.
Axiom proof_of_rat_mul_safety_wit_19_out_undef : rat_mul_safety_wit_19_out_undef.
Axiom proof_of_rat_mul_safety_wit_20_out_undef : rat_mul_safety_wit_20_out_undef.
Axiom proof_of_rat_mul_return_wit_1_out_known : rat_mul_return_wit_1_out_known.
Axiom proof_of_rat_mul_return_wit_2_out_known : rat_mul_return_wit_2_out_known.
Axiom proof_of_rat_mul_return_wit_3_out_known : rat_mul_return_wit_3_out_known.
Axiom proof_of_rat_mul_return_wit_4_out_known : rat_mul_return_wit_4_out_known.
Axiom proof_of_rat_mul_return_wit_5_out_undef : rat_mul_return_wit_5_out_undef.
Axiom proof_of_rat_mul_return_wit_6_out_undef : rat_mul_return_wit_6_out_undef.
Axiom proof_of_rat_mul_return_wit_7_out_undef : rat_mul_return_wit_7_out_undef.
Axiom proof_of_rat_mul_return_wit_8_out_undef : rat_mul_return_wit_8_out_undef.
Axiom proof_of_rat_mul_return_wit_9_out_known : rat_mul_return_wit_9_out_known.
Axiom proof_of_rat_mul_return_wit_10_out_undef : rat_mul_return_wit_10_out_undef.
Axiom proof_of_rat_mul_return_wit_11_out_known : rat_mul_return_wit_11_out_known.
Axiom proof_of_rat_mul_return_wit_12_out_undef : rat_mul_return_wit_12_out_undef.
Axiom proof_of_rat_mul_partial_solve_wit_1_out_known_pure : rat_mul_partial_solve_wit_1_out_known_pure.
Axiom proof_of_rat_mul_partial_solve_wit_1_out_known : rat_mul_partial_solve_wit_1_out_known.
Axiom proof_of_rat_mul_partial_solve_wit_2_out_undef_pure : rat_mul_partial_solve_wit_2_out_undef_pure.
Axiom proof_of_rat_mul_partial_solve_wit_2_out_undef : rat_mul_partial_solve_wit_2_out_undef.
Axiom proof_of_rat_mul_partial_solve_wit_3_out_known_pure : rat_mul_partial_solve_wit_3_out_known_pure.
Axiom proof_of_rat_mul_partial_solve_wit_3_out_known : rat_mul_partial_solve_wit_3_out_known.
Axiom proof_of_rat_mul_partial_solve_wit_4_out_undef_pure : rat_mul_partial_solve_wit_4_out_undef_pure.
Axiom proof_of_rat_mul_partial_solve_wit_4_out_undef : rat_mul_partial_solve_wit_4_out_undef.
Axiom proof_of_rat_mul_partial_solve_wit_5_out_known_pure : rat_mul_partial_solve_wit_5_out_known_pure.
Axiom proof_of_rat_mul_partial_solve_wit_5_out_known : rat_mul_partial_solve_wit_5_out_known.
Axiom proof_of_rat_mul_partial_solve_wit_6_out_undef_pure : rat_mul_partial_solve_wit_6_out_undef_pure.
Axiom proof_of_rat_mul_partial_solve_wit_6_out_undef : rat_mul_partial_solve_wit_6_out_undef.

End VC_Correct.
