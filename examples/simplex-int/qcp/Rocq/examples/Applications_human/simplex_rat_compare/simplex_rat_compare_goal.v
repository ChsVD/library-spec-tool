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
Require Import SimpleC.EE.Applications_human.simplex_rat_compare.simplex_rat_compare_lib.
Local Open Scope sac.

(*----- Function rat_compare -----*)

Definition rat_compare_safety_wit_1_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ False ”
.

Definition rat_compare_safety_wit_2_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ False ”
.

Definition rat_compare_safety_wit_3_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ False ”
.

Definition rat_compare_safety_wit_4_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ False ”
.

Definition rat_compare_safety_wit_5_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_compare_safety_wit_6_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_compare_safety_wit_7_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ False ”
.

Definition rat_compare_safety_wit_8_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ False ”
.

Definition rat_compare_safety_wit_9_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ False ”
.

Definition rat_compare_safety_wit_10_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ False ”
.

Definition rat_compare_safety_wit_11_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_compare_safety_wit_12_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_compare_safety_wit_13_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_compare_safety_wit_14_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 1)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_compare_safety_wit_15_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH7 : (retval = 1)) (PreH8 : ((INT_MIN) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((INT_MIN) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= D_out_known)) (PreH15 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition rat_compare_safety_wit_16_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH7 : (retval = 1)) (PreH8 : ((INT_MIN) <= A_out_known)) (PreH9 : (A_out_known <= INT_MAX)) (PreH10 : ((INT_MIN) <= C_out_known)) (PreH11 : (C_out_known <= INT_MAX)) (PreH12 : (1 <= B_out_known)) (PreH13 : (B_out_known <= INT_MAX)) (PreH14 : (1 <= D_out_known)) (PreH15 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_17_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : ((INT_MIN) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((INT_MIN) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= D_out_undef)) (PreH15 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition rat_compare_safety_wit_18_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH4 : (retval_2 = 1)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH7 : (retval = 1)) (PreH8 : ((INT_MIN) <= A_out_undef)) (PreH9 : (A_out_undef <= INT_MAX)) (PreH10 : ((INT_MIN) <= C_out_undef)) (PreH11 : (C_out_undef <= INT_MAX)) (PreH12 : (1 <= B_out_undef)) (PreH13 : (B_out_undef <= INT_MAX)) (PreH14 : (1 <= D_out_undef)) (PreH15 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_19_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> (-1))
|--
  “ False ”
.

Definition rat_compare_safety_wit_20_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> (-1))
|--
  “ False ”
.

Definition rat_compare_safety_wit_21_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_22_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_23_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 1)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_24_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 1)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_25_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> (-1))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_26_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> (-1))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_27_out_known := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_known * B_out_known ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_safety_wit_28_out_undef := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |-> (C_out_undef * B_out_undef ))
  **  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rat_compare_return_wit_1_out_known := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 1)
|--
  “ (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_compare_return_wit_1_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_1_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) > (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_2_out_undef := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 1)
|--
  “ (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_compare_return_wit_2_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_2_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) > (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_3_out_known := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> (-1))
|--
  “ (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ ((-1) = (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_compare_return_wit_3_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_3_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) < (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((-1) = (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_4_out_undef := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> (-1))
|--
  “ (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ ((-1) = (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_compare_return_wit_4_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_4_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) < (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((-1) = (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_5_out_known := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (1 = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (0 = (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_compare_return_wit_5_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  (1 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_5_out_known_split_goal_2 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_known * D_out_known ) <= (C_out_known * B_out_known ))) (PreH2 : ((A_out_known * D_out_known ) >= (C_out_known * B_out_known ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_known)) (PreH10 : (A_out_known <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_known)) (PreH12 : (C_out_known <= INT_MAX)) (PreH13 : (1 <= B_out_known)) (PreH14 : (B_out_known <= INT_MAX)) (PreH15 : (1 <= D_out_known)) (PreH16 : (D_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_compare_order (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_6_out_undef := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> 0)
|--
  “ (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (1 = 1) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |-> (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (0 = (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_compare_return_wit_6_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  (1 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_6_out_undef_split_goal_2 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : ((A_out_undef * D_out_undef ) <= (C_out_undef * B_out_undef ))) (PreH2 : ((A_out_undef * D_out_undef ) >= (C_out_undef * B_out_undef ))) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH5 : (retval_2 = 1)) (PreH6 : (retval <> 0)) (PreH7 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH8 : (retval = 1)) (PreH9 : ((INT_MIN) <= A_out_undef)) (PreH10 : (A_out_undef <= INT_MAX)) (PreH11 : ((INT_MIN) <= C_out_undef)) (PreH12 : (C_out_undef <= INT_MAX)) (PreH13 : (1 <= B_out_undef)) (PreH14 : (B_out_undef <= INT_MAX)) (PreH15 : (1 <= D_out_undef)) (PreH16 : (D_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_compare_order (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_7_out_known := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (0 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_compare_return_wit_7_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_known) (B_out_known)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_known)) (PreH8 : (A_out_known <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_known)) (PreH10 : (C_out_known <= INT_MAX)) (PreH11 : (1 <= B_out_known)) (PreH12 : (B_out_known <= INT_MAX)) (PreH13 : (1 <= D_out_known)) (PreH14 : (D_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_8_out_undef := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (0 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_compare_return_wit_8_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (checked_mul_flag (C_out_undef) (B_out_undef)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH6 : (retval = 1)) (PreH7 : ((INT_MIN) <= A_out_undef)) (PreH8 : (A_out_undef <= INT_MAX)) (PreH9 : ((INT_MIN) <= C_out_undef)) (PreH10 : (C_out_undef <= INT_MAX)) (PreH11 : (1 <= B_out_undef)) (PreH12 : (B_out_undef <= INT_MAX)) (PreH13 : (1 <= D_out_undef)) (PreH14 : (D_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_return_wit_9_out_known := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (0 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
) \/
(
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known))) ”
  &&  emp
).

Definition rat_compare_return_wit_9_out_known_split_goal_1 := 
forall (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  (0 = (simplex_rat_compare_flag (A_out_known) (B_out_known) (C_out_known) (D_out_known)))
.

Definition rat_compare_return_wit_10_out_undef := 
(
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (0 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ” 
  &&  “ (0 = 0) ”
  &&  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
) \/
(
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  TT && emp 
|--
  “ (0 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef))) ”
  &&  emp
).

Definition rat_compare_return_wit_10_out_undef_split_goal_1 := 
forall (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 0)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  (0 = (simplex_rat_compare_flag (A_out_undef) (B_out_undef) (C_out_undef) (D_out_undef)))
.

Definition rat_compare_partial_solve_wit_1_out_known_pure := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((INT_MIN) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= D_out_known)) (PreH8 : (D_out_known <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (A_out_known = A_out_known) ” 
  &&  “ (D_out_known = D_out_known) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ”
.

Definition rat_compare_partial_solve_wit_1_out_known_aux := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (PreH1 : ((INT_MIN) <= A_out_known)) (PreH2 : (A_out_known <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_known)) (PreH4 : (C_out_known <= INT_MAX)) (PreH5 : (1 <= B_out_known)) (PreH6 : (B_out_known <= INT_MAX)) (PreH7 : (1 <= D_out_known)) (PreH8 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (A_out_known = A_out_known) ” 
  &&  “ (D_out_known = D_out_known) ” 
  &&  “ ((INT_MIN) <= A_out_known) ” 
  &&  “ (A_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_known) ” 
  &&  “ (D_out_known <= INT_MAX) ” 
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
  **  ((order_pre) # Int  |-> old_out_known)
.

Definition rat_compare_partial_solve_wit_1_out_known := rat_compare_partial_solve_wit_1_out_known_pure -> rat_compare_partial_solve_wit_1_out_known_aux.

Definition rat_compare_partial_solve_wit_2_out_undef_pure := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((INT_MIN) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= D_out_undef)) (PreH8 : (D_out_undef <= INT_MAX)) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (A_out_undef = A_out_undef) ” 
  &&  “ (D_out_undef = D_out_undef) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ”
.

Definition rat_compare_partial_solve_wit_2_out_undef_aux := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (PreH1 : ((INT_MIN) <= A_out_undef)) (PreH2 : (A_out_undef <= INT_MAX)) (PreH3 : ((INT_MIN) <= C_out_undef)) (PreH4 : (C_out_undef <= INT_MAX)) (PreH5 : (1 <= B_out_undef)) (PreH6 : (B_out_undef <= INT_MAX)) (PreH7 : (1 <= D_out_undef)) (PreH8 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (A_out_undef = A_out_undef) ” 
  &&  “ (D_out_undef = D_out_undef) ” 
  &&  “ ((INT_MIN) <= A_out_undef) ” 
  &&  “ (A_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= D_out_undef) ” 
  &&  “ (D_out_undef <= INT_MAX) ” 
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
  **  ((order_pre) # Int  |->_)
.

Definition rat_compare_partial_solve_wit_2_out_undef := rat_compare_partial_solve_wit_2_out_undef_pure -> rat_compare_partial_solve_wit_2_out_undef_aux.

Definition rat_compare_partial_solve_wit_3_out_known_pure := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_known * D_out_known ))
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (C_out_known = C_out_known) ” 
  &&  “ (B_out_known = B_out_known) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ”
.

Definition rat_compare_partial_solve_wit_3_out_known_aux := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (old_out_known: Z) (D_out_known: Z) (C_out_known: Z) (B_out_known: Z) (A_out_known: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_known) (D_out_known)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_known)) (PreH5 : (A_out_known <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_known)) (PreH7 : (C_out_known <= INT_MAX)) (PreH8 : (1 <= B_out_known)) (PreH9 : (B_out_known <= INT_MAX)) (PreH10 : (1 <= D_out_known)) (PreH11 : (D_out_known <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_known)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_known)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_known)
  **  ((order_pre) # Int  |-> old_out_known)
|--
  “ (C_out_known = C_out_known) ” 
  &&  “ (B_out_known = B_out_known) ” 
  &&  “ ((INT_MIN) <= C_out_known) ” 
  &&  “ (C_out_known <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_known) ” 
  &&  “ (B_out_known <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_known) (D_out_known))) ” 
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
  **  ((order_pre) # Int  |-> old_out_known)
.

Definition rat_compare_partial_solve_wit_3_out_known := rat_compare_partial_solve_wit_3_out_known_pure -> rat_compare_partial_solve_wit_3_out_known_aux.

Definition rat_compare_partial_solve_wit_4_out_undef_pure := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((( &( "p" ) )) # Int  |-> (A_out_undef * D_out_undef ))
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((( &( "order" ) )) # Ptr  |-> order_pre)
  **  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (C_out_undef = C_out_undef) ” 
  &&  “ (B_out_undef = B_out_undef) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ”
.

Definition rat_compare_partial_solve_wit_4_out_undef_aux := 
forall (order_pre: Z) (y_pre: Z) (x_pre: Z) (D_out_undef: Z) (C_out_undef: Z) (B_out_undef: Z) (A_out_undef: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (checked_mul_flag (A_out_undef) (D_out_undef)))) (PreH3 : (retval = 1)) (PreH4 : ((INT_MIN) <= A_out_undef)) (PreH5 : (A_out_undef <= INT_MAX)) (PreH6 : ((INT_MIN) <= C_out_undef)) (PreH7 : (C_out_undef <= INT_MAX)) (PreH8 : (1 <= B_out_undef)) (PreH9 : (B_out_undef <= INT_MAX)) (PreH10 : (1 <= D_out_undef)) (PreH11 : (D_out_undef <= INT_MAX)) ,
  ((&((x_pre)  # "SxRat" ->ₛ "num")) # Int  |-> A_out_undef)
  **  ((&((x_pre)  # "SxRat" ->ₛ "den")) # Int  |-> B_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "num")) # Int  |-> C_out_undef)
  **  ((&((y_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D_out_undef)
  **  ((order_pre) # Int  |->_)
|--
  “ (C_out_undef = C_out_undef) ” 
  &&  “ (B_out_undef = B_out_undef) ” 
  &&  “ ((INT_MIN) <= C_out_undef) ” 
  &&  “ (C_out_undef <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= B_out_undef) ” 
  &&  “ (B_out_undef <= INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (checked_mul_flag (A_out_undef) (D_out_undef))) ” 
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
  **  ((order_pre) # Int  |->_)
.

Definition rat_compare_partial_solve_wit_4_out_undef := rat_compare_partial_solve_wit_4_out_undef_pure -> rat_compare_partial_solve_wit_4_out_undef_aux.

Module Type VC_Correct.


Axiom proof_of_rat_compare_safety_wit_1_out_known : rat_compare_safety_wit_1_out_known.
Axiom proof_of_rat_compare_safety_wit_2_out_known : rat_compare_safety_wit_2_out_known.
Axiom proof_of_rat_compare_safety_wit_3_out_undef : rat_compare_safety_wit_3_out_undef.
Axiom proof_of_rat_compare_safety_wit_4_out_undef : rat_compare_safety_wit_4_out_undef.
Axiom proof_of_rat_compare_safety_wit_5_out_known : rat_compare_safety_wit_5_out_known.
Axiom proof_of_rat_compare_safety_wit_6_out_undef : rat_compare_safety_wit_6_out_undef.
Axiom proof_of_rat_compare_safety_wit_7_out_known : rat_compare_safety_wit_7_out_known.
Axiom proof_of_rat_compare_safety_wit_8_out_known : rat_compare_safety_wit_8_out_known.
Axiom proof_of_rat_compare_safety_wit_9_out_undef : rat_compare_safety_wit_9_out_undef.
Axiom proof_of_rat_compare_safety_wit_10_out_undef : rat_compare_safety_wit_10_out_undef.
Axiom proof_of_rat_compare_safety_wit_11_out_known : rat_compare_safety_wit_11_out_known.
Axiom proof_of_rat_compare_safety_wit_12_out_undef : rat_compare_safety_wit_12_out_undef.
Axiom proof_of_rat_compare_safety_wit_13_out_known : rat_compare_safety_wit_13_out_known.
Axiom proof_of_rat_compare_safety_wit_14_out_undef : rat_compare_safety_wit_14_out_undef.
Axiom proof_of_rat_compare_safety_wit_15_out_known : rat_compare_safety_wit_15_out_known.
Axiom proof_of_rat_compare_safety_wit_16_out_known : rat_compare_safety_wit_16_out_known.
Axiom proof_of_rat_compare_safety_wit_17_out_undef : rat_compare_safety_wit_17_out_undef.
Axiom proof_of_rat_compare_safety_wit_18_out_undef : rat_compare_safety_wit_18_out_undef.
Axiom proof_of_rat_compare_safety_wit_19_out_known : rat_compare_safety_wit_19_out_known.
Axiom proof_of_rat_compare_safety_wit_20_out_undef : rat_compare_safety_wit_20_out_undef.
Axiom proof_of_rat_compare_safety_wit_21_out_known : rat_compare_safety_wit_21_out_known.
Axiom proof_of_rat_compare_safety_wit_22_out_undef : rat_compare_safety_wit_22_out_undef.
Axiom proof_of_rat_compare_safety_wit_23_out_known : rat_compare_safety_wit_23_out_known.
Axiom proof_of_rat_compare_safety_wit_24_out_undef : rat_compare_safety_wit_24_out_undef.
Axiom proof_of_rat_compare_safety_wit_25_out_known : rat_compare_safety_wit_25_out_known.
Axiom proof_of_rat_compare_safety_wit_26_out_undef : rat_compare_safety_wit_26_out_undef.
Axiom proof_of_rat_compare_safety_wit_27_out_known : rat_compare_safety_wit_27_out_known.
Axiom proof_of_rat_compare_safety_wit_28_out_undef : rat_compare_safety_wit_28_out_undef.
Axiom proof_of_rat_compare_return_wit_1_out_known : rat_compare_return_wit_1_out_known.
Axiom proof_of_rat_compare_return_wit_2_out_undef : rat_compare_return_wit_2_out_undef.
Axiom proof_of_rat_compare_return_wit_3_out_known : rat_compare_return_wit_3_out_known.
Axiom proof_of_rat_compare_return_wit_4_out_undef : rat_compare_return_wit_4_out_undef.
Axiom proof_of_rat_compare_return_wit_5_out_known : rat_compare_return_wit_5_out_known.
Axiom proof_of_rat_compare_return_wit_6_out_undef : rat_compare_return_wit_6_out_undef.
Axiom proof_of_rat_compare_return_wit_7_out_known : rat_compare_return_wit_7_out_known.
Axiom proof_of_rat_compare_return_wit_8_out_undef : rat_compare_return_wit_8_out_undef.
Axiom proof_of_rat_compare_return_wit_9_out_known : rat_compare_return_wit_9_out_known.
Axiom proof_of_rat_compare_return_wit_10_out_undef : rat_compare_return_wit_10_out_undef.
Axiom proof_of_rat_compare_partial_solve_wit_1_out_known_pure : rat_compare_partial_solve_wit_1_out_known_pure.
Axiom proof_of_rat_compare_partial_solve_wit_1_out_known : rat_compare_partial_solve_wit_1_out_known.
Axiom proof_of_rat_compare_partial_solve_wit_2_out_undef_pure : rat_compare_partial_solve_wit_2_out_undef_pure.
Axiom proof_of_rat_compare_partial_solve_wit_2_out_undef : rat_compare_partial_solve_wit_2_out_undef.
Axiom proof_of_rat_compare_partial_solve_wit_3_out_known_pure : rat_compare_partial_solve_wit_3_out_known_pure.
Axiom proof_of_rat_compare_partial_solve_wit_3_out_known : rat_compare_partial_solve_wit_3_out_known.
Axiom proof_of_rat_compare_partial_solve_wit_4_out_undef_pure : rat_compare_partial_solve_wit_4_out_undef_pure.
Axiom proof_of_rat_compare_partial_solve_wit_4_out_undef : rat_compare_partial_solve_wit_4_out_undef.

End VC_Correct.
