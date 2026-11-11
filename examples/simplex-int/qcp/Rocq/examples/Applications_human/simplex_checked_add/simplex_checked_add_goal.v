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
Require Import SimpleC.EE.Applications_human.simplex_checked_add.simplex_checked_add_lib.
Local Open Scope sac.

(*----- Function checked_add -----*)

Definition checked_add_safety_wit_1 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_add_safety_wit_2 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_add_safety_wit_3 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_add_safety_wit_4 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_add_safety_wit_5 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_6 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_7 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_8 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = A)) (PreH2 : (y_pre = B)) (PreH3 : ((INT_MIN) <= x_pre)) (PreH4 : (x_pre <= INT_MAX)) (PreH5 : ((INT_MIN) <= y_pre)) (PreH6 : (y_pre <= INT_MAX)) (PreH7 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_9 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_add_safety_wit_10 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition checked_add_safety_wit_11 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_add_safety_wit_12 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_add_safety_wit_13 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_14 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_15 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_16 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_17 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_18 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_19 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_20 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_21 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_22 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_23 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre > 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((INT_MAX - y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (INT_MAX - y_pre )) ”
.

Definition checked_add_safety_wit_24 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre > 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((INT_MAX - y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (INT_MAX - y_pre )) ”
.

Definition checked_add_safety_wit_25 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre > 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_26 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre > 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_27 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_28 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_29 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <= 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_30 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre <= 0)) (PreH2 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre = A)) (PreH5 : (y_pre = B)) (PreH6 : ((INT_MIN) <= x_pre)) (PreH7 : (x_pre <= INT_MAX)) (PreH8 : ((INT_MIN) <= y_pre)) (PreH9 : (y_pre <= INT_MAX)) (PreH10 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_31 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_32 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre <= (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_33 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ False ”
.

Definition checked_add_safety_wit_34 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ False ”
.

Definition checked_add_safety_wit_35 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (((-INT_MAX) - y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - y_pre )) ”
.

Definition checked_add_safety_wit_36 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (((-INT_MAX) - y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-INT_MAX) - y_pre )) ”
.

Definition checked_add_safety_wit_37 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_add_safety_wit_38 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition checked_add_safety_wit_39 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_40 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre < 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition checked_add_safety_wit_41 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_42 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition checked_add_safety_wit_43 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition checked_add_safety_wit_44 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition checked_add_safety_wit_45 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition checked_add_safety_wit_46 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition checked_add_safety_wit_47 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |->_)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition checked_add_safety_wit_48 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> old)
|--
  “ ((x_pre + y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x_pre + y_pre )) ”
.

Definition checked_add_safety_wit_49 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_50 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_51 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_52 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_53 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_safety_wit_54 := 
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "y" ) )) # Int  |-> y_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition checked_add_return_wit_1 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 = (checked_add_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A + B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  (1 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_2 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 = (checked_add_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A + B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (x_pre <= (INT_MAX - y_pre ))) (PreH3 : (y_pre > 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  (1 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_3 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 = (checked_add_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A + B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  (1 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_4 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 = (checked_add_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A + B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_4_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre >= 0)) (PreH2 : (y_pre <= 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  (1 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_5 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 = (checked_add_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A + B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  TT && emp 
|--
  “ (1 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_5_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  (1 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_6 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((out_pre) # Int  |-> (x_pre + y_pre ))
|--
  “ (1 = (checked_add_flag (A) (B))) ” 
  &&  “ (1 = 1) ”
  &&  ((out_pre) # Int  |-> (A + B ))
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  TT && emp 
|--
  “ (1 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_6_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre >= ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  (1 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_7 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_7_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 0)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_8 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_8_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre < ((-INT_MAX) - y_pre ))) (PreH2 : (y_pre < 0)) (PreH3 : (y_pre <= 0)) (PreH4 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH6 : (x_pre = A)) (PreH7 : (y_pre = B)) (PreH8 : ((INT_MIN) <= x_pre)) (PreH9 : (x_pre <= INT_MAX)) (PreH10 : ((INT_MIN) <= y_pre)) (PreH11 : (y_pre <= INT_MAX)) (PreH12 : (known = 1)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_9 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_9_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 1)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_10 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_10_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre > (INT_MAX - y_pre ))) (PreH2 : (y_pre > 0)) (PreH3 : (y_pre <> ((-INT_MAX) - 1 ))) (PreH4 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH5 : (x_pre = A)) (PreH6 : (y_pre = B)) (PreH7 : ((INT_MIN) <= x_pre)) (PreH8 : (x_pre <= INT_MAX)) (PreH9 : ((INT_MIN) <= y_pre)) (PreH10 : (y_pre <= INT_MAX)) (PreH11 : (known = 0)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_11 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_11_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 0)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_12 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_12_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (x_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre = A)) (PreH3 : (y_pre = B)) (PreH4 : ((INT_MIN) <= x_pre)) (PreH5 : (x_pre <= INT_MAX)) (PreH6 : ((INT_MIN) <= y_pre)) (PreH7 : (y_pre <= INT_MAX)) (PreH8 : (known = 1)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_13 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (old: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  ((out_pre) # Int  |-> old)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 1) ”
  &&  ((out_pre) # Int  |-> old)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_13_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 1)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Definition checked_add_return_wit_14 := 
(
forall (out_pre: Z) (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  ((out_pre) # Int  |->_)
|--
  “ (0 = (checked_add_flag (A) (B))) ” 
  &&  “ (0 = 0) ” 
  &&  “ (known = 0) ”
  &&  ((out_pre) # Int  |->_)
) \/
(
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  TT && emp 
|--
  “ (0 = (checked_add_flag (x_pre) (y_pre))) ”
  &&  emp
).

Definition checked_add_return_wit_14_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (known: Z) (B: Z) (A: Z) (PreH1 : (y_pre = ((-INT_MAX) - 1 ))) (PreH2 : (x_pre <> ((-INT_MAX) - 1 ))) (PreH3 : (x_pre = A)) (PreH4 : (y_pre = B)) (PreH5 : ((INT_MIN) <= x_pre)) (PreH6 : (x_pre <= INT_MAX)) (PreH7 : ((INT_MIN) <= y_pre)) (PreH8 : (y_pre <= INT_MAX)) (PreH9 : (known = 0)) ,
  (0 = (checked_add_flag (x_pre) (y_pre)))
.

Module Type VC_Correct.


Axiom proof_of_checked_add_safety_wit_1 : checked_add_safety_wit_1.
Axiom proof_of_checked_add_safety_wit_2 : checked_add_safety_wit_2.
Axiom proof_of_checked_add_safety_wit_3 : checked_add_safety_wit_3.
Axiom proof_of_checked_add_safety_wit_4 : checked_add_safety_wit_4.
Axiom proof_of_checked_add_safety_wit_5 : checked_add_safety_wit_5.
Axiom proof_of_checked_add_safety_wit_6 : checked_add_safety_wit_6.
Axiom proof_of_checked_add_safety_wit_7 : checked_add_safety_wit_7.
Axiom proof_of_checked_add_safety_wit_8 : checked_add_safety_wit_8.
Axiom proof_of_checked_add_safety_wit_9 : checked_add_safety_wit_9.
Axiom proof_of_checked_add_safety_wit_10 : checked_add_safety_wit_10.
Axiom proof_of_checked_add_safety_wit_11 : checked_add_safety_wit_11.
Axiom proof_of_checked_add_safety_wit_12 : checked_add_safety_wit_12.
Axiom proof_of_checked_add_safety_wit_13 : checked_add_safety_wit_13.
Axiom proof_of_checked_add_safety_wit_14 : checked_add_safety_wit_14.
Axiom proof_of_checked_add_safety_wit_15 : checked_add_safety_wit_15.
Axiom proof_of_checked_add_safety_wit_16 : checked_add_safety_wit_16.
Axiom proof_of_checked_add_safety_wit_17 : checked_add_safety_wit_17.
Axiom proof_of_checked_add_safety_wit_18 : checked_add_safety_wit_18.
Axiom proof_of_checked_add_safety_wit_19 : checked_add_safety_wit_19.
Axiom proof_of_checked_add_safety_wit_20 : checked_add_safety_wit_20.
Axiom proof_of_checked_add_safety_wit_21 : checked_add_safety_wit_21.
Axiom proof_of_checked_add_safety_wit_22 : checked_add_safety_wit_22.
Axiom proof_of_checked_add_safety_wit_23 : checked_add_safety_wit_23.
Axiom proof_of_checked_add_safety_wit_24 : checked_add_safety_wit_24.
Axiom proof_of_checked_add_safety_wit_25 : checked_add_safety_wit_25.
Axiom proof_of_checked_add_safety_wit_26 : checked_add_safety_wit_26.
Axiom proof_of_checked_add_safety_wit_27 : checked_add_safety_wit_27.
Axiom proof_of_checked_add_safety_wit_28 : checked_add_safety_wit_28.
Axiom proof_of_checked_add_safety_wit_29 : checked_add_safety_wit_29.
Axiom proof_of_checked_add_safety_wit_30 : checked_add_safety_wit_30.
Axiom proof_of_checked_add_safety_wit_31 : checked_add_safety_wit_31.
Axiom proof_of_checked_add_safety_wit_32 : checked_add_safety_wit_32.
Axiom proof_of_checked_add_safety_wit_33 : checked_add_safety_wit_33.
Axiom proof_of_checked_add_safety_wit_34 : checked_add_safety_wit_34.
Axiom proof_of_checked_add_safety_wit_35 : checked_add_safety_wit_35.
Axiom proof_of_checked_add_safety_wit_36 : checked_add_safety_wit_36.
Axiom proof_of_checked_add_safety_wit_37 : checked_add_safety_wit_37.
Axiom proof_of_checked_add_safety_wit_38 : checked_add_safety_wit_38.
Axiom proof_of_checked_add_safety_wit_39 : checked_add_safety_wit_39.
Axiom proof_of_checked_add_safety_wit_40 : checked_add_safety_wit_40.
Axiom proof_of_checked_add_safety_wit_41 : checked_add_safety_wit_41.
Axiom proof_of_checked_add_safety_wit_42 : checked_add_safety_wit_42.
Axiom proof_of_checked_add_safety_wit_43 : checked_add_safety_wit_43.
Axiom proof_of_checked_add_safety_wit_44 : checked_add_safety_wit_44.
Axiom proof_of_checked_add_safety_wit_45 : checked_add_safety_wit_45.
Axiom proof_of_checked_add_safety_wit_46 : checked_add_safety_wit_46.
Axiom proof_of_checked_add_safety_wit_47 : checked_add_safety_wit_47.
Axiom proof_of_checked_add_safety_wit_48 : checked_add_safety_wit_48.
Axiom proof_of_checked_add_safety_wit_49 : checked_add_safety_wit_49.
Axiom proof_of_checked_add_safety_wit_50 : checked_add_safety_wit_50.
Axiom proof_of_checked_add_safety_wit_51 : checked_add_safety_wit_51.
Axiom proof_of_checked_add_safety_wit_52 : checked_add_safety_wit_52.
Axiom proof_of_checked_add_safety_wit_53 : checked_add_safety_wit_53.
Axiom proof_of_checked_add_safety_wit_54 : checked_add_safety_wit_54.
Axiom proof_of_checked_add_return_wit_1 : checked_add_return_wit_1.
Axiom proof_of_checked_add_return_wit_2 : checked_add_return_wit_2.
Axiom proof_of_checked_add_return_wit_3 : checked_add_return_wit_3.
Axiom proof_of_checked_add_return_wit_4 : checked_add_return_wit_4.
Axiom proof_of_checked_add_return_wit_5 : checked_add_return_wit_5.
Axiom proof_of_checked_add_return_wit_6 : checked_add_return_wit_6.
Axiom proof_of_checked_add_return_wit_7 : checked_add_return_wit_7.
Axiom proof_of_checked_add_return_wit_8 : checked_add_return_wit_8.
Axiom proof_of_checked_add_return_wit_9 : checked_add_return_wit_9.
Axiom proof_of_checked_add_return_wit_10 : checked_add_return_wit_10.
Axiom proof_of_checked_add_return_wit_11 : checked_add_return_wit_11.
Axiom proof_of_checked_add_return_wit_12 : checked_add_return_wit_12.
Axiom proof_of_checked_add_return_wit_13 : checked_add_return_wit_13.
Axiom proof_of_checked_add_return_wit_14 : checked_add_return_wit_14.

End VC_Correct.
