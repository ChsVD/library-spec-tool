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
Require Import SimpleC.EE.Applications_human.simplex_positive_gcd.simplex_positive_gcd_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_reduce.simplex_rat_reduce_lib.
Local Open Scope sac.

(*----- Function rat_reduce -----*)

Definition rat_reduce_safety_wit_1 := 
forall (r_pre: Z) (D: Z) (N: Z) (PreH1 : ((-INT_MAX) <= N)) (PreH2 : (N <= INT_MAX)) (PreH3 : (1 <= D)) (PreH4 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rat_reduce_safety_wit_2 := 
forall (r_pre: Z) (D: Z) (N: Z) (PreH1 : (N < 0)) (PreH2 : ((-INT_MAX) <= N)) (PreH3 : (N <= INT_MAX)) (PreH4 : (1 <= D)) (PreH5 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (N <> (INT_MIN)) ”
.

Definition rat_reduce_safety_wit_3 := 
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((N <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((N <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition rat_reduce_safety_wit_3_split_goal_1 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((N <> (INT_MIN)) \/ (retval <> (-1))) ”
.

Definition rat_reduce_safety_wit_3_split_goal_2 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (retval <> 0) ”
.

Definition rat_reduce_safety_wit_4 := 
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((N <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((N <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition rat_reduce_safety_wit_4_split_goal_1 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((N <> (INT_MIN)) \/ (retval <> (-1))) ”
.

Definition rat_reduce_safety_wit_4_split_goal_2 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (retval <> 0) ”
.

Definition rat_reduce_safety_wit_5 := 
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((D <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((D <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition rat_reduce_safety_wit_5_split_goal_1 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((D <> (INT_MIN)) \/ (retval <> (-1))) ”
.

Definition rat_reduce_safety_wit_5_split_goal_2 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (retval <> 0) ”
.

Definition rat_reduce_safety_wit_6 := 
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((D <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
) \/
(
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((D <> (INT_MIN)) \/ (retval <> (-1))) ” 
  &&  “ (retval <> 0) ”
).

Definition rat_reduce_safety_wit_6_split_goal_1 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((D <> (INT_MIN)) \/ (retval <> (-1))) ”
.

Definition rat_reduce_safety_wit_6_split_goal_2 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (retval <> 0) ”
.

Definition rat_reduce_return_wit_1 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd ((-N)) (D)))) (PreH2 : (N < 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (D ÷ retval ))
|--
  (EX (P: Z)  (Q: Z) ,
  “ (simplex_rat_reduce_result N D P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((N * Q ) = (P * D )) ” 
  &&  “ (N <> 0) ” 
  &&  “ ((Zgcd ((Zabs (N))) (D)) <> 1) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q))
  ||
  (EX (P: Z)  (Q: Z) ,
  “ (simplex_rat_reduce_result N D P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((N * Q ) = (P * D )) ” 
  &&  “ (N <> 0) ” 
  &&  “ (P = N) ” 
  &&  “ (Q = D) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q))
.

Definition rat_reduce_return_wit_2 := 
forall (r_pre: Z) (D: Z) (N: Z) (retval: Z) (PreH1 : (retval = (Zgcd (N) (D)))) (PreH2 : (N >= 0)) (PreH3 : ((-INT_MAX) <= N)) (PreH4 : (N <= INT_MAX)) (PreH5 : (1 <= D)) (PreH6 : (D <= INT_MAX)) ,
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> (N ÷ retval ))
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> (D ÷ retval ))
|--
  (EX (P: Z)  (Q: Z) ,
  “ (simplex_rat_reduce_result N D P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((N * Q ) = (P * D )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ” 
  &&  “ ((Zgcd ((Zabs (N))) (D)) <> 1) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q))
  ||
  (EX (P: Z)  (Q: Z) ,
  “ (simplex_rat_reduce_result N D P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((N * Q ) = (P * D )) ” 
  &&  “ (P = 0) ” 
  &&  “ (Q = 1) ” 
  &&  “ (P = N) ” 
  &&  “ (Q = D) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q))
  ||
  (EX (P: Z)  (Q: Z) ,
  “ (simplex_rat_reduce_result N D P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((N * Q ) = (P * D )) ” 
  &&  “ (N <> 0) ” 
  &&  “ ((Zgcd ((Zabs (N))) (D)) <> 1) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q))
  ||
  (EX (P: Z)  (Q: Z) ,
  “ (simplex_rat_reduce_result N D P Q ) ” 
  &&  “ ((-INT_MAX) <= P) ” 
  &&  “ (P <= INT_MAX) ” 
  &&  “ (1 <= Q) ” 
  &&  “ (Q <= INT_MAX) ” 
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ” 
  &&  “ ((N * Q ) = (P * D )) ” 
  &&  “ (N <> 0) ” 
  &&  “ (P = N) ” 
  &&  “ (Q = D) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> P)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> Q))
.

Definition rat_reduce_partial_solve_wit_1_pure := 
forall (r_pre: Z) (D: Z) (N: Z) (PreH1 : (N < 0)) (PreH2 : ((-INT_MAX) <= N)) (PreH3 : (N <= INT_MAX)) (PreH4 : (1 <= D)) (PreH5 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> (-N))
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((-N) = (-N)) ” 
  &&  “ (D = D) ” 
  &&  “ (0 <= (-N)) ” 
  &&  “ ((-N) <= INT_MAX) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D <= INT_MAX) ”
.

Definition rat_reduce_partial_solve_wit_1_aux := 
forall (r_pre: Z) (D: Z) (N: Z) (PreH1 : (N < 0)) (PreH2 : ((-INT_MAX) <= N)) (PreH3 : (N <= INT_MAX)) (PreH4 : (1 <= D)) (PreH5 : (D <= INT_MAX)) ,
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ ((-N) = (-N)) ” 
  &&  “ (D = D) ” 
  &&  “ (0 <= (-N)) ” 
  &&  “ ((-N) <= INT_MAX) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D <= INT_MAX) ” 
  &&  “ (N < 0) ” 
  &&  “ ((-INT_MAX) <= N) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (1 <= D) ” 
  &&  “ (D <= INT_MAX) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
.

Definition rat_reduce_partial_solve_wit_1 := rat_reduce_partial_solve_wit_1_pure -> rat_reduce_partial_solve_wit_1_aux.

Definition rat_reduce_partial_solve_wit_2_pure := 
forall (r_pre: Z) (D: Z) (N: Z) (PreH1 : (N >= 0)) (PreH2 : ((-INT_MAX) <= N)) (PreH3 : (N <= INT_MAX)) (PreH4 : (1 <= D)) (PreH5 : (D <= INT_MAX)) ,
  ((( &( "g" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> N)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (N = N) ” 
  &&  “ (D = D) ” 
  &&  “ (0 <= N) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D <= INT_MAX) ”
.

Definition rat_reduce_partial_solve_wit_2_aux := 
forall (r_pre: Z) (D: Z) (N: Z) (PreH1 : (N >= 0)) (PreH2 : ((-INT_MAX) <= N)) (PreH3 : (N <= INT_MAX)) (PreH4 : (1 <= D)) (PreH5 : (D <= INT_MAX)) ,
  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  “ (N = N) ” 
  &&  “ (D = D) ” 
  &&  “ (0 <= N) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (0 <= D) ” 
  &&  “ (D <= INT_MAX) ” 
  &&  “ (N >= 0) ” 
  &&  “ ((-INT_MAX) <= N) ” 
  &&  “ (N <= INT_MAX) ” 
  &&  “ (1 <= D) ” 
  &&  “ (D <= INT_MAX) ”
  &&  ((&((r_pre)  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&((r_pre)  # "SxRat" ->ₛ "den")) # Int  |-> D)
.

Definition rat_reduce_partial_solve_wit_2 := rat_reduce_partial_solve_wit_2_pure -> rat_reduce_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_rat_reduce_safety_wit_1 : rat_reduce_safety_wit_1.
Axiom proof_of_rat_reduce_safety_wit_2 : rat_reduce_safety_wit_2.
Axiom proof_of_rat_reduce_safety_wit_3 : rat_reduce_safety_wit_3.
Axiom proof_of_rat_reduce_safety_wit_4 : rat_reduce_safety_wit_4.
Axiom proof_of_rat_reduce_safety_wit_5 : rat_reduce_safety_wit_5.
Axiom proof_of_rat_reduce_safety_wit_6 : rat_reduce_safety_wit_6.
Axiom proof_of_rat_reduce_return_wit_1 : rat_reduce_return_wit_1.
Axiom proof_of_rat_reduce_return_wit_2 : rat_reduce_return_wit_2.
Axiom proof_of_rat_reduce_partial_solve_wit_1_pure : rat_reduce_partial_solve_wit_1_pure.
Axiom proof_of_rat_reduce_partial_solve_wit_1 : rat_reduce_partial_solve_wit_1.
Axiom proof_of_rat_reduce_partial_solve_wit_2_pure : rat_reduce_partial_solve_wit_2_pure.
Axiom proof_of_rat_reduce_partial_solve_wit_2 : rat_reduce_partial_solve_wit_2.

End VC_Correct.
