From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_mul.simplex_rat_mul_lib.
Require Import SimpleC.EE.Applications_human.simplex_rat_add.simplex_rat_add_lib.
Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib.
Local Open Scope sac.

(*----- Function sx_recompute -----*)

Definition sx_recompute_safety_wit_1_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (s_pre: Z) (PreH1 : (s_pre = S_recompute)) (PreH2 : (0 <= R_recompute)) (PreH3 : (R_recompute <= 16)) (PreH4 : (0 <= V_recompute)) (PreH5 : (V_recompute <= 24)) (PreH6 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH7 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH8 : ((Zlength (RN_recompute)) = R_recompute)) (PreH9 : ((Zlength (RD_recompute)) = R_recompute)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH11 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH12 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH13 : (Forall (Z.le (1)) AD_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH15 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH17 : (Forall (Z.le (1)) RD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) VN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) VN_recompute )) (PreH21 : (Forall (Z.le (1)) VD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) VD_recompute )) (PreH23 : ((Zlength (VN_recompute)) = V_recompute)) (PreH24 : ((Zlength (VD_recompute)) = V_recompute)),
  (UndefStructPredSxRat ( &( "product" ) ) )
  **  (UndefStructPredSxRat ( &( "sum" ) ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs s_pre R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix s_pre R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values s_pre V_recompute VN_recompute VD_recompute )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_2_zero_rows :=
forall (S_zero_rows: Z) (s_pre: Z) (PreH1 : (s_pre = S_zero_rows)),
  (UndefStructPredSxRat ( &( "product" ) ) )
  **  (UndefStructPredSxRat ( &( "sum" ) ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_3_zero_rows :=
forall (S_zero_rows: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (i = 0)),
  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ False ”
.

Definition sx_recompute_safety_wit_4_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < R_recompute)) (PreH3 : (0 <= R_recompute)) (PreH4 : (R_recompute <= 16)) (PreH5 : (0 <= V_recompute)) (PreH6 : (V_recompute <= 24)) (PreH7 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH8 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (RN_recompute)) = R_recompute)) (PreH10 : ((Zlength (RD_recompute)) = R_recompute)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH12 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH13 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH14 : (Forall (Z.le (1)) AD_recompute )) (PreH15 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH16 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH18 : (Forall (Z.le (1)) RD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH21 : (Forall (Z.ge (INT_MAX)) CN )) (PreH22 : (Forall (Z.le (1)) CD )) (PreH23 : (Forall (Z.ge (INT_MAX)) CD )) (PreH24 : ((Zlength (CN)) = V_recompute)) (PreH25 : ((Zlength (CD)) = V_recompute)) (PreH26 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )),
  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_5_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : ((Znth j IB_recompute 0) = 0)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j < V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN )) (PreH25 : (Forall (Z.le (1)) CD )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD )) (PreH27 : ((-INT_MAX) <= N)) (PreH28 : (N <= INT_MAX)) (PreH29 : (1 <= D)) (PreH30 : (D <= INT_MAX)) (PreH31 : ((Zlength (CN)) = V_recompute)) (PreH32 : ((Zlength (CD)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_6_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 1)) (PreH4 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH5 : ((-INT_MAX) <= P)) (PreH6 : (P <= INT_MAX)) (PreH7 : (1 <= Q)) (PreH8 : (Q <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH10 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH11 : (P = 0)) (PreH12 : (Q = 1)) (PreH13 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH14 : ((Znth j IB_recompute 0) = 0)) (PreH15 : (0 <= i)) (PreH16 : (i < R_recompute)) (PreH17 : (0 <= j)) (PreH18 : (j < V_recompute)) (PreH19 : (0 <= R_recompute)) (PreH20 : (R_recompute <= 16)) (PreH21 : (0 <= V_recompute)) (PreH22 : (V_recompute <= 24)) (PreH23 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH25 : ((Zlength (RN_recompute)) = R_recompute)) (PreH26 : ((Zlength (RD_recompute)) = R_recompute)) (PreH27 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH28 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH29 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH30 : (Forall (Z.le (1)) AD_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH32 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH33 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH34 : (Forall (Z.le (1)) RD_recompute )) (PreH35 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH36 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH37 : (Forall (Z.ge (INT_MAX)) CN )) (PreH38 : (Forall (Z.le (1)) CD )) (PreH39 : (Forall (Z.ge (INT_MAX)) CD )) (PreH40 : ((-INT_MAX) <= N)) (PreH41 : (N <= INT_MAX)) (PreH42 : (1 <= D)) (PreH43 : (D <= INT_MAX)) (PreH44 : ((Zlength (CN)) = V_recompute)) (PreH45 : ((Zlength (CD)) = V_recompute)) (PreH46 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH47 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ False ”
.

Definition sx_recompute_safety_wit_7_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 1)) (PreH4 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH5 : ((-INT_MAX) <= P)) (PreH6 : (P <= INT_MAX)) (PreH7 : (1 <= Q)) (PreH8 : (Q <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH10 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH11 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH12 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH13 : ((Znth j IB_recompute 0) = 0)) (PreH14 : (0 <= i)) (PreH15 : (i < R_recompute)) (PreH16 : (0 <= j)) (PreH17 : (j < V_recompute)) (PreH18 : (0 <= R_recompute)) (PreH19 : (R_recompute <= 16)) (PreH20 : (0 <= V_recompute)) (PreH21 : (V_recompute <= 24)) (PreH22 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH23 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (RN_recompute)) = R_recompute)) (PreH25 : ((Zlength (RD_recompute)) = R_recompute)) (PreH26 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH27 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH28 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH29 : (Forall (Z.le (1)) AD_recompute )) (PreH30 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH31 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH33 : (Forall (Z.le (1)) RD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH36 : (Forall (Z.ge (INT_MAX)) CN )) (PreH37 : (Forall (Z.le (1)) CD )) (PreH38 : (Forall (Z.ge (INT_MAX)) CD )) (PreH39 : ((-INT_MAX) <= N)) (PreH40 : (N <= INT_MAX)) (PreH41 : (1 <= D)) (PreH42 : (D <= INT_MAX)) (PreH43 : ((Zlength (CN)) = V_recompute)) (PreH44 : ((Zlength (CD)) = V_recompute)) (PreH45 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH46 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ False ”
.

Definition sx_recompute_safety_wit_8_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 0)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH5 : ((Znth j IB_recompute 0) = 0)) (PreH6 : (0 <= i)) (PreH7 : (i < R_recompute)) (PreH8 : (0 <= j)) (PreH9 : (j < V_recompute)) (PreH10 : (0 <= R_recompute)) (PreH11 : (R_recompute <= 16)) (PreH12 : (0 <= V_recompute)) (PreH13 : (V_recompute <= 24)) (PreH14 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH15 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH16 : ((Zlength (RN_recompute)) = R_recompute)) (PreH17 : ((Zlength (RD_recompute)) = R_recompute)) (PreH18 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH19 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH21 : (Forall (Z.le (1)) AD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH24 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH25 : (Forall (Z.le (1)) RD_recompute )) (PreH26 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH27 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH28 : (Forall (Z.ge (INT_MAX)) CN )) (PreH29 : (Forall (Z.le (1)) CD )) (PreH30 : (Forall (Z.ge (INT_MAX)) CD )) (PreH31 : ((-INT_MAX) <= N)) (PreH32 : (N <= INT_MAX)) (PreH33 : (1 <= D)) (PreH34 : (D <= INT_MAX)) (PreH35 : ((Zlength (CN)) = V_recompute)) (PreH36 : ((Zlength (CD)) = V_recompute)) (PreH37 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH38 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ False ”
.

Definition sx_recompute_safety_wit_9_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 0)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH5 : ((Znth j IB_recompute 0) = 0)) (PreH6 : (0 <= i)) (PreH7 : (i < R_recompute)) (PreH8 : (0 <= j)) (PreH9 : (j < V_recompute)) (PreH10 : (0 <= R_recompute)) (PreH11 : (R_recompute <= 16)) (PreH12 : (0 <= V_recompute)) (PreH13 : (V_recompute <= 24)) (PreH14 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH15 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH16 : ((Zlength (RN_recompute)) = R_recompute)) (PreH17 : ((Zlength (RD_recompute)) = R_recompute)) (PreH18 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH19 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH21 : (Forall (Z.le (1)) AD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH24 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH25 : (Forall (Z.le (1)) RD_recompute )) (PreH26 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH27 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH28 : (Forall (Z.ge (INT_MAX)) CN )) (PreH29 : (Forall (Z.le (1)) CD )) (PreH30 : (Forall (Z.ge (INT_MAX)) CD )) (PreH31 : ((-INT_MAX) <= N)) (PreH32 : (N <= INT_MAX)) (PreH33 : (1 <= D)) (PreH34 : (D <= INT_MAX)) (PreH35 : ((Zlength (CN)) = V_recompute)) (PreH36 : ((Zlength (CD)) = V_recompute)) (PreH37 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH38 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_10_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (P_2 = 0)) (PreH12 : (Q_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH15 : (retval = 1)) (PreH16 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH17 : ((-INT_MAX) <= P)) (PreH18 : (P <= INT_MAX)) (PreH19 : (1 <= Q)) (PreH20 : (Q <= INT_MAX)) (PreH21 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH22 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH23 : (P = 0)) (PreH24 : (Q = 1)) (PreH25 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH26 : ((Znth j IB_recompute 0) = 0)) (PreH27 : (0 <= i)) (PreH28 : (i < R_recompute)) (PreH29 : (0 <= j)) (PreH30 : (j < V_recompute)) (PreH31 : (0 <= R_recompute)) (PreH32 : (R_recompute <= 16)) (PreH33 : (0 <= V_recompute)) (PreH34 : (V_recompute <= 24)) (PreH35 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH37 : ((Zlength (RN_recompute)) = R_recompute)) (PreH38 : ((Zlength (RD_recompute)) = R_recompute)) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH40 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH42 : (Forall (Z.le (1)) AD_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH44 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH46 : (Forall (Z.le (1)) RD_recompute )) (PreH47 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH48 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH49 : (Forall (Z.ge (INT_MAX)) CN )) (PreH50 : (Forall (Z.le (1)) CD )) (PreH51 : (Forall (Z.ge (INT_MAX)) CD )) (PreH52 : ((-INT_MAX) <= N)) (PreH53 : (N <= INT_MAX)) (PreH54 : (1 <= D)) (PreH55 : (D <= INT_MAX)) (PreH56 : ((Zlength (CN)) = V_recompute)) (PreH57 : ((Zlength (CD)) = V_recompute)) (PreH58 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH59 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ False ”
.

Definition sx_recompute_safety_wit_11_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (((N * Q ) + (P * D ) ) <> 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH22 : (P = 0)) (PreH23 : (Q = 1)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN )) (PreH49 : (Forall (Z.le (1)) CD )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD )) (PreH51 : ((-INT_MAX) <= N)) (PreH52 : (N <= INT_MAX)) (PreH53 : (1 <= D)) (PreH54 : (D <= INT_MAX)) (PreH55 : ((Zlength (CN)) = V_recompute)) (PreH56 : ((Zlength (CD)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ False ”
.

Definition sx_recompute_safety_wit_12_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH6 : (retval = 1)) (PreH7 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH8 : ((-INT_MAX) <= P)) (PreH9 : (P <= INT_MAX)) (PreH10 : (1 <= Q)) (PreH11 : (Q <= INT_MAX)) (PreH12 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH13 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH14 : (P = 0)) (PreH15 : (Q = 1)) (PreH16 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH17 : ((Znth j IB_recompute 0) = 0)) (PreH18 : (0 <= i)) (PreH19 : (i < R_recompute)) (PreH20 : (0 <= j)) (PreH21 : (j < V_recompute)) (PreH22 : (0 <= R_recompute)) (PreH23 : (R_recompute <= 16)) (PreH24 : (0 <= V_recompute)) (PreH25 : (V_recompute <= 24)) (PreH26 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH27 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH28 : ((Zlength (RN_recompute)) = R_recompute)) (PreH29 : ((Zlength (RD_recompute)) = R_recompute)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH31 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH33 : (Forall (Z.le (1)) AD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH36 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH37 : (Forall (Z.le (1)) RD_recompute )) (PreH38 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH39 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH40 : (Forall (Z.ge (INT_MAX)) CN )) (PreH41 : (Forall (Z.le (1)) CD )) (PreH42 : (Forall (Z.ge (INT_MAX)) CD )) (PreH43 : ((-INT_MAX) <= N)) (PreH44 : (N <= INT_MAX)) (PreH45 : (1 <= D)) (PreH46 : (D <= INT_MAX)) (PreH47 : ((Zlength (CN)) = V_recompute)) (PreH48 : ((Zlength (CD)) = V_recompute)) (PreH49 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH50 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ False ”
.

Definition sx_recompute_safety_wit_13_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (P_2 = 0)) (PreH12 : (Q_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH15 : (retval = 1)) (PreH16 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH17 : ((-INT_MAX) <= P)) (PreH18 : (P <= INT_MAX)) (PreH19 : (1 <= Q)) (PreH20 : (Q <= INT_MAX)) (PreH21 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH22 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH23 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN )) (PreH49 : (Forall (Z.le (1)) CD )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD )) (PreH51 : ((-INT_MAX) <= N)) (PreH52 : (N <= INT_MAX)) (PreH53 : (1 <= D)) (PreH54 : (D <= INT_MAX)) (PreH55 : ((Zlength (CN)) = V_recompute)) (PreH56 : ((Zlength (CD)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ False ”
.

Definition sx_recompute_safety_wit_14_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (((N * Q ) + (P * D ) ) <> 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH22 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH23 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH24 : ((Znth j IB_recompute 0) = 0)) (PreH25 : (0 <= i)) (PreH26 : (i < R_recompute)) (PreH27 : (0 <= j)) (PreH28 : (j < V_recompute)) (PreH29 : (0 <= R_recompute)) (PreH30 : (R_recompute <= 16)) (PreH31 : (0 <= V_recompute)) (PreH32 : (V_recompute <= 24)) (PreH33 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH34 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (RN_recompute)) = R_recompute)) (PreH36 : ((Zlength (RD_recompute)) = R_recompute)) (PreH37 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH38 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH40 : (Forall (Z.le (1)) AD_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH42 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH44 : (Forall (Z.le (1)) RD_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH46 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH47 : (Forall (Z.ge (INT_MAX)) CN )) (PreH48 : (Forall (Z.le (1)) CD )) (PreH49 : (Forall (Z.ge (INT_MAX)) CD )) (PreH50 : ((-INT_MAX) <= N)) (PreH51 : (N <= INT_MAX)) (PreH52 : (1 <= D)) (PreH53 : (D <= INT_MAX)) (PreH54 : ((Zlength (CN)) = V_recompute)) (PreH55 : ((Zlength (CD)) = V_recompute)) (PreH56 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH57 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ False ”
.

Definition sx_recompute_safety_wit_15_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH6 : (retval = 1)) (PreH7 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH8 : ((-INT_MAX) <= P)) (PreH9 : (P <= INT_MAX)) (PreH10 : (1 <= Q)) (PreH11 : (Q <= INT_MAX)) (PreH12 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH13 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH14 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH15 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH16 : ((Znth j IB_recompute 0) = 0)) (PreH17 : (0 <= i)) (PreH18 : (i < R_recompute)) (PreH19 : (0 <= j)) (PreH20 : (j < V_recompute)) (PreH21 : (0 <= R_recompute)) (PreH22 : (R_recompute <= 16)) (PreH23 : (0 <= V_recompute)) (PreH24 : (V_recompute <= 24)) (PreH25 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH26 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH27 : ((Zlength (RN_recompute)) = R_recompute)) (PreH28 : ((Zlength (RD_recompute)) = R_recompute)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH30 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH32 : (Forall (Z.le (1)) AD_recompute )) (PreH33 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH34 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH35 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH36 : (Forall (Z.le (1)) RD_recompute )) (PreH37 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH38 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH39 : (Forall (Z.ge (INT_MAX)) CN )) (PreH40 : (Forall (Z.le (1)) CD )) (PreH41 : (Forall (Z.ge (INT_MAX)) CD )) (PreH42 : ((-INT_MAX) <= N)) (PreH43 : (N <= INT_MAX)) (PreH44 : (1 <= D)) (PreH45 : (D <= INT_MAX)) (PreH46 : ((Zlength (CN)) = V_recompute)) (PreH47 : ((Zlength (CD)) = V_recompute)) (PreH48 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH49 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ False ”
.

Definition sx_recompute_safety_wit_16_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH6 : (retval = 1)) (PreH7 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH8 : ((-INT_MAX) <= P)) (PreH9 : (P <= INT_MAX)) (PreH10 : (1 <= Q)) (PreH11 : (Q <= INT_MAX)) (PreH12 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH13 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH14 : (P = 0)) (PreH15 : (Q = 1)) (PreH16 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH17 : ((Znth j IB_recompute 0) = 0)) (PreH18 : (0 <= i)) (PreH19 : (i < R_recompute)) (PreH20 : (0 <= j)) (PreH21 : (j < V_recompute)) (PreH22 : (0 <= R_recompute)) (PreH23 : (R_recompute <= 16)) (PreH24 : (0 <= V_recompute)) (PreH25 : (V_recompute <= 24)) (PreH26 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH27 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH28 : ((Zlength (RN_recompute)) = R_recompute)) (PreH29 : ((Zlength (RD_recompute)) = R_recompute)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH31 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH33 : (Forall (Z.le (1)) AD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH36 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH37 : (Forall (Z.le (1)) RD_recompute )) (PreH38 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH39 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH40 : (Forall (Z.ge (INT_MAX)) CN )) (PreH41 : (Forall (Z.le (1)) CD )) (PreH42 : (Forall (Z.ge (INT_MAX)) CD )) (PreH43 : ((-INT_MAX) <= N)) (PreH44 : (N <= INT_MAX)) (PreH45 : (1 <= D)) (PreH46 : (D <= INT_MAX)) (PreH47 : ((Zlength (CN)) = V_recompute)) (PreH48 : ((Zlength (CD)) = V_recompute)) (PreH49 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH50 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_17_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH6 : (retval = 1)) (PreH7 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH8 : ((-INT_MAX) <= P)) (PreH9 : (P <= INT_MAX)) (PreH10 : (1 <= Q)) (PreH11 : (Q <= INT_MAX)) (PreH12 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH13 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH14 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH15 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH16 : ((Znth j IB_recompute 0) = 0)) (PreH17 : (0 <= i)) (PreH18 : (i < R_recompute)) (PreH19 : (0 <= j)) (PreH20 : (j < V_recompute)) (PreH21 : (0 <= R_recompute)) (PreH22 : (R_recompute <= 16)) (PreH23 : (0 <= V_recompute)) (PreH24 : (V_recompute <= 24)) (PreH25 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH26 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH27 : ((Zlength (RN_recompute)) = R_recompute)) (PreH28 : ((Zlength (RD_recompute)) = R_recompute)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH30 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH32 : (Forall (Z.le (1)) AD_recompute )) (PreH33 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH34 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH35 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH36 : (Forall (Z.le (1)) RD_recompute )) (PreH37 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH38 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH39 : (Forall (Z.ge (INT_MAX)) CN )) (PreH40 : (Forall (Z.le (1)) CD )) (PreH41 : (Forall (Z.ge (INT_MAX)) CD )) (PreH42 : ((-INT_MAX) <= N)) (PreH43 : (N <= INT_MAX)) (PreH44 : (1 <= D)) (PreH45 : (D <= INT_MAX)) (PreH46 : ((Zlength (CN)) = V_recompute)) (PreH47 : ((Zlength (CD)) = V_recompute)) (PreH48 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH49 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_recompute_safety_wit_18_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (P_2 = 0)) (PreH12 : (Q_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH15 : (retval = 1)) (PreH16 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH17 : ((-INT_MAX) <= P)) (PreH18 : (P <= INT_MAX)) (PreH19 : (1 <= Q)) (PreH20 : (Q <= INT_MAX)) (PreH21 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH22 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH23 : (P = 0)) (PreH24 : (Q = 1)) (PreH25 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH26 : ((Znth j IB_recompute 0) = 0)) (PreH27 : (0 <= i)) (PreH28 : (i < R_recompute)) (PreH29 : (0 <= j)) (PreH30 : (j < V_recompute)) (PreH31 : (0 <= R_recompute)) (PreH32 : (R_recompute <= 16)) (PreH33 : (0 <= V_recompute)) (PreH34 : (V_recompute <= 24)) (PreH35 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH37 : ((Zlength (RN_recompute)) = R_recompute)) (PreH38 : ((Zlength (RD_recompute)) = R_recompute)) (PreH39 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH40 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH42 : (Forall (Z.le (1)) AD_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH44 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH46 : (Forall (Z.le (1)) RD_recompute )) (PreH47 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH48 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH49 : (Forall (Z.ge (INT_MAX)) CN )) (PreH50 : (Forall (Z.le (1)) CD )) (PreH51 : (Forall (Z.ge (INT_MAX)) CD )) (PreH52 : ((-INT_MAX) <= N)) (PreH53 : (N <= INT_MAX)) (PreH54 : (1 <= D)) (PreH55 : (D <= INT_MAX)) (PreH56 : ((Zlength (CN)) = V_recompute)) (PreH57 : ((Zlength (CD)) = V_recompute)) (PreH58 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH59 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_recompute_safety_wit_19_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (((N * Q ) + (P * D ) ) <> 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH22 : (P = 0)) (PreH23 : (Q = 1)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN )) (PreH49 : (Forall (Z.le (1)) CD )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD )) (PreH51 : ((-INT_MAX) <= N)) (PreH52 : (N <= INT_MAX)) (PreH53 : (1 <= D)) (PreH54 : (D <= INT_MAX)) (PreH55 : ((Zlength (CN)) = V_recompute)) (PreH56 : ((Zlength (CD)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_recompute_safety_wit_20_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (P_2 = 0)) (PreH12 : (Q_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH15 : (retval = 1)) (PreH16 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH17 : ((-INT_MAX) <= P)) (PreH18 : (P <= INT_MAX)) (PreH19 : (1 <= Q)) (PreH20 : (Q <= INT_MAX)) (PreH21 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH22 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH23 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN )) (PreH49 : (Forall (Z.le (1)) CD )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD )) (PreH51 : ((-INT_MAX) <= N)) (PreH52 : (N <= INT_MAX)) (PreH53 : (1 <= D)) (PreH54 : (D <= INT_MAX)) (PreH55 : ((Zlength (CN)) = V_recompute)) (PreH56 : ((Zlength (CD)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_recompute_safety_wit_21_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N D P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N * Q ) + (P * D ) ) * Q_2 ) = (P_2 * (D * Q ) ))) (PreH11 : (((N * Q ) + (P * D ) ) <> 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH22 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH23 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH24 : ((Znth j IB_recompute 0) = 0)) (PreH25 : (0 <= i)) (PreH26 : (i < R_recompute)) (PreH27 : (0 <= j)) (PreH28 : (j < V_recompute)) (PreH29 : (0 <= R_recompute)) (PreH30 : (R_recompute <= 16)) (PreH31 : (0 <= V_recompute)) (PreH32 : (V_recompute <= 24)) (PreH33 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH34 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (RN_recompute)) = R_recompute)) (PreH36 : ((Zlength (RD_recompute)) = R_recompute)) (PreH37 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH38 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH40 : (Forall (Z.le (1)) AD_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH42 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH44 : (Forall (Z.le (1)) RD_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH46 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH47 : (Forall (Z.ge (INT_MAX)) CN )) (PreH48 : (Forall (Z.le (1)) CD )) (PreH49 : (Forall (Z.ge (INT_MAX)) CD )) (PreH50 : ((-INT_MAX) <= N)) (PreH51 : (N <= INT_MAX)) (PreH52 : (1 <= D)) (PreH53 : (D <= INT_MAX)) (PreH54 : ((Zlength (CN)) = V_recompute)) (PreH55 : ((Zlength (CD)) = V_recompute)) (PreH56 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH57 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_recompute_safety_wit_22_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : ((Znth j IB_recompute 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j < V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN )) (PreH25 : (Forall (Z.le (1)) CD )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD )) (PreH27 : ((-INT_MAX) <= N)) (PreH28 : (N <= INT_MAX)) (PreH29 : (1 <= D)) (PreH30 : (D <= INT_MAX)) (PreH31 : ((Zlength (CN)) = V_recompute)) (PreH32 : ((Zlength (CD)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_recompute_safety_wit_23_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) = 0)) (PreH2 : ((Znth j IB_recompute 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < R_recompute)) (PreH5 : (0 <= j)) (PreH6 : (j < V_recompute)) (PreH7 : (0 <= R_recompute)) (PreH8 : (R_recompute <= 16)) (PreH9 : (0 <= V_recompute)) (PreH10 : (V_recompute <= 24)) (PreH11 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH13 : ((Zlength (RN_recompute)) = R_recompute)) (PreH14 : ((Zlength (RD_recompute)) = R_recompute)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH16 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH18 : (Forall (Z.le (1)) AD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH21 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH22 : (Forall (Z.le (1)) RD_recompute )) (PreH23 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH24 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH25 : (Forall (Z.ge (INT_MAX)) CN )) (PreH26 : (Forall (Z.le (1)) CD )) (PreH27 : (Forall (Z.ge (INT_MAX)) CD )) (PreH28 : ((-INT_MAX) <= N)) (PreH29 : (N <= INT_MAX)) (PreH30 : (1 <= D)) (PreH31 : (D <= INT_MAX)) (PreH32 : ((Zlength (CN)) = V_recompute)) (PreH33 : ((Zlength (CD)) = V_recompute)) (PreH34 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH35 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_recompute_safety_wit_24_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < R_recompute)) (PreH3 : (0 <= V_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN )) (PreH23 : (Forall (Z.le (1)) CD )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD )) (PreH25 : ((-INT_MAX) <= N)) (PreH26 : (N <= INT_MAX)) (PreH27 : (1 <= D)) (PreH28 : (D <= INT_MAX)) (PreH29 : ((Zlength (CN)) = V_recompute)) (PreH30 : ((Zlength (CD)) = V_recompute)) (PreH31 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH32 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i V_recompute N D )),
  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> V_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (((&((S_recompute)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (Znth (i) (B_recompute) (0)))
  **  (IntArray.missing_i &((S_recompute)  # "SxState" ->ₛ "basic") i 0 R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD (Znth (i) (B_recompute) (0)) )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sx_recompute_safety_wit_25_zero_rows :=
forall (S_zero_rows: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (i = 0)),
  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_recompute_safety_wit_26_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CD: (@list Z)) (CN: (@list Z)) (i: Z) (PreH1 : (i >= R_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i <= R_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN )) (PreH23 : (Forall (Z.le (1)) CD )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD )) (PreH25 : ((Zlength (CN)) = V_recompute)) (PreH26 : ((Zlength (CD)) = V_recompute)) (PreH27 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )),
  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_recompute_entail_wit_1_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (s_pre: Z) (PreH1 : (s_pre = S_recompute)) (PreH2 : (0 <= R_recompute)) (PreH3 : (R_recompute <= 16)) (PreH4 : (0 <= V_recompute)) (PreH5 : (V_recompute <= 24)) (PreH6 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH7 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH8 : ((Zlength (RN_recompute)) = R_recompute)) (PreH9 : ((Zlength (RD_recompute)) = R_recompute)) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH11 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH12 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH13 : (Forall (Z.le (1)) AD_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH15 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH17 : (Forall (Z.le (1)) RD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) VN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) VN_recompute )) (PreH21 : (Forall (Z.le (1)) VD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) VD_recompute )) (PreH23 : ((Zlength (VN_recompute)) = V_recompute)) (PreH24 : ((Zlength (VD_recompute)) = V_recompute)),
  (UndefStructPredSxRat ( &( "product" ) ) )
  **  (UndefStructPredSxRat ( &( "sum" ) ) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs s_pre R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix s_pre R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values s_pre V_recompute VN_recompute VD_recompute )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= 0) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute 0 V_recompute 1 CN CD ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (s_pre: Z) (PreH1 : (V_recompute <= INT_MAX)) (PreH2 : (R_recompute <= INT_MAX)) (PreH3 : (V_recompute >= INT_MIN)) (PreH4 : (R_recompute >= INT_MIN)) (PreH5 : (s_pre = S_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) VN_recompute )) (PreH24 : (Forall (Z.ge (INT_MAX)) VN_recompute )) (PreH25 : (Forall (Z.le (1)) VD_recompute )) (PreH26 : (Forall (Z.ge (INT_MAX)) VD_recompute )) (PreH27 : ((Zlength (VN_recompute)) = V_recompute)) (PreH28 : ((Zlength (VD_recompute)) = V_recompute)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs s_pre R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix s_pre R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values s_pre V_recompute VN_recompute VD_recompute )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (s_pre = S_recompute) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute 0 V_recompute 1 CN CD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_2_zero_rows :=
forall (S_zero_rows: Z) (s_pre: Z) (PreH1 : (s_pre = S_zero_rows)),
  (UndefStructPredSxRat ( &( "product" ) ) )
  **  (UndefStructPredSxRat ( &( "sum" ) ) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
|--
  “ (0 = 0) ”
  &&  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
.

Definition sx_recompute_entail_wit_3_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CD_2: (@list Z)) (CN_2: (@list Z)) (i: Z) (PreH1 : (i < R_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i <= R_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH23 : (Forall (Z.le (1)) CD_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH25 : ((Zlength (CN_2)) = V_recompute)) (PreH26 : ((Zlength (CD_2)) = V_recompute)) (PreH27 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )),
  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CD_2: (@list Z)) (CN_2: (@list Z)) (i: Z) (PreH1 : (i < R_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i <= R_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH23 : (Forall (Z.le (1)) CD_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH25 : ((Zlength (CN_2)) = V_recompute)) (PreH26 : ((Zlength (CD_2)) = V_recompute)) (PreH27 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )),
  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_4_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < R_recompute)) (PreH3 : (0 <= R_recompute)) (PreH4 : (R_recompute <= 16)) (PreH5 : (0 <= V_recompute)) (PreH6 : (V_recompute <= 24)) (PreH7 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH8 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (RN_recompute)) = R_recompute)) (PreH10 : ((Zlength (RD_recompute)) = R_recompute)) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH12 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH13 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH14 : (Forall (Z.le (1)) AD_recompute )) (PreH15 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH16 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH18 : (Forall (Z.le (1)) RD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH21 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH22 : (Forall (Z.le (1)) CD_2 )) (PreH23 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH24 : ((Zlength (CN_2)) = V_recompute)) (PreH25 : ((Zlength (CD_2)) = V_recompute)) (PreH26 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )),
  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i 0 N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (i: Z) (PreH1 : ((Znth (i) (RN_recompute) (0)) <= INT_MAX)) (PreH2 : ((Znth (i) (RD_recompute) (0)) <= INT_MAX)) (PreH3 : ((Znth (i) (RN_recompute) (0)) >= INT_MIN)) (PreH4 : ((Znth (i) (RD_recompute) (0)) >= INT_MIN)) (PreH5 : (0 <= i)) (PreH6 : (i < R_recompute)) (PreH7 : (0 <= R_recompute)) (PreH8 : (R_recompute <= 16)) (PreH9 : (0 <= V_recompute)) (PreH10 : (V_recompute <= 24)) (PreH11 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH13 : ((Zlength (RN_recompute)) = R_recompute)) (PreH14 : ((Zlength (RD_recompute)) = R_recompute)) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH16 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH18 : (Forall (Z.le (1)) AD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH21 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH22 : (Forall (Z.le (1)) RD_recompute )) (PreH23 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH24 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH25 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH26 : (Forall (Z.le (1)) CD_2 )) (PreH27 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH28 : ((Zlength (CN_2)) = V_recompute)) (PreH29 : ((Zlength (CD_2)) = V_recompute)) (PreH30 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )),
  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= (Znth (i) (RN_recompute) (0))) ”
  &&  “ ((Znth (i) (RN_recompute) (0)) <= INT_MAX) ”
  &&  “ (1 <= (Znth (i) (RD_recompute) (0))) ”
  &&  “ ((Znth (i) (RD_recompute) (0)) <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i 0 (Znth (i) (RN_recompute) (0)) (Znth (i) (RD_recompute) (0)) ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_5_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (D_2: Z) (N_2: Z) (CD_2: (@list Z)) (CN_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < V_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j <= V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH25 : (Forall (Z.le (1)) CD_2 )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH27 : ((-INT_MAX) <= N_2)) (PreH28 : (N_2 <= INT_MAX)) (PreH29 : (1 <= D_2)) (PreH30 : (D_2 <= INT_MAX)) (PreH31 : ((Zlength (CN_2)) = V_recompute)) (PreH32 : ((Zlength (CD_2)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D_2)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= j) ”
  &&  “ (j < V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (D_2: Z) (N_2: Z) (CD_2: (@list Z)) (CN_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < V_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j <= V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH25 : (Forall (Z.le (1)) CD_2 )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH27 : ((-INT_MAX) <= N_2)) (PreH28 : (N_2 <= INT_MAX)) (PreH29 : (1 <= D_2)) (PreH30 : (D_2 <= INT_MAX)) (PreH31 : ((Zlength (CN_2)) = V_recompute)) (PreH32 : ((Zlength (CD_2)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= j) ”
  &&  “ (j < V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N_2) ”
  &&  “ (N_2 <= INT_MAX) ”
  &&  “ (1 <= D_2) ”
  &&  “ (D_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N_2 D_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
).

Definition sx_recompute_entail_wit_6_1_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH11 : (P_2 = 0)) (PreH12 : (Q_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH15 : (retval = 1)) (PreH16 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH17 : ((-INT_MAX) <= P)) (PreH18 : (P <= INT_MAX)) (PreH19 : (1 <= Q)) (PreH20 : (Q <= INT_MAX)) (PreH21 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH22 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH23 : (P = 0)) (PreH24 : (Q = 1)) (PreH25 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH26 : ((Znth j IB_recompute 0) = 0)) (PreH27 : (0 <= i)) (PreH28 : (i < R_recompute)) (PreH29 : (0 <= j)) (PreH30 : (j < V_recompute)) (PreH31 : (0 <= R_recompute)) (PreH32 : (R_recompute <= 16)) (PreH33 : (0 <= V_recompute)) (PreH34 : (V_recompute <= 24)) (PreH35 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH37 : ((Zlength (RN_recompute)) = R_recompute)) (PreH38 : ((Zlength (RD_recompute)) = R_recompute)) (PreH39 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH40 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH42 : (Forall (Z.le (1)) AD_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH44 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH46 : (Forall (Z.le (1)) RD_recompute )) (PreH47 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH48 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH49 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH50 : (Forall (Z.le (1)) CD_2 )) (PreH51 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH52 : ((-INT_MAX) <= N_2)) (PreH53 : (N_2 <= INT_MAX)) (PreH54 : (1 <= D_2)) (PreH55 : (D_2 <= INT_MAX)) (PreH56 : ((Zlength (CN_2)) = V_recompute)) (PreH57 : ((Zlength (CD_2)) = V_recompute)) (PreH58 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH59 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : ((Znth (j) (CD_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD_2) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval_2 <> 0)) (PreH10 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH11 : (retval_2 = 1)) (PreH12 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH13 : ((-INT_MAX) <= P_2)) (PreH14 : (P_2 <= INT_MAX)) (PreH15 : (1 <= Q_2)) (PreH16 : (Q_2 <= INT_MAX)) (PreH17 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH18 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH19 : (P_2 = 0)) (PreH20 : (Q_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH23 : (retval = 1)) (PreH24 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH25 : ((-INT_MAX) <= P)) (PreH26 : (P <= INT_MAX)) (PreH27 : (1 <= Q)) (PreH28 : (Q <= INT_MAX)) (PreH29 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH30 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH31 : (P = 0)) (PreH32 : (Q = 1)) (PreH33 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH34 : ((Znth j IB_recompute 0) = 0)) (PreH35 : (0 <= i)) (PreH36 : (i < R_recompute)) (PreH37 : (0 <= j)) (PreH38 : (j < V_recompute)) (PreH39 : (0 <= R_recompute)) (PreH40 : (R_recompute <= 16)) (PreH41 : (0 <= V_recompute)) (PreH42 : (V_recompute <= 24)) (PreH43 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH44 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH45 : ((Zlength (RN_recompute)) = R_recompute)) (PreH46 : ((Zlength (RD_recompute)) = R_recompute)) (PreH47 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH48 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH49 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH50 : (Forall (Z.le (1)) AD_recompute )) (PreH51 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH52 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH53 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH54 : (Forall (Z.le (1)) RD_recompute )) (PreH55 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH56 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH57 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH58 : (Forall (Z.le (1)) CD_2 )) (PreH59 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH60 : ((-INT_MAX) <= N_2)) (PreH61 : (N_2 <= INT_MAX)) (PreH62 : (1 <= D_2)) (PreH63 : (D_2 <= INT_MAX)) (PreH64 : ((Zlength (CN_2)) = V_recompute)) (PreH65 : ((Zlength (CD_2)) = V_recompute)) (PreH66 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH67 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= P_2) ”
  &&  “ (P_2 <= INT_MAX) ”
  &&  “ (1 <= Q_2) ”
  &&  “ (Q_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) P_2 Q_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_6_2_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH11 : (((N_2 * Q ) + (P * D_2 ) ) <> 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH22 : (P = 0)) (PreH23 : (Q = 1)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH49 : (Forall (Z.le (1)) CD_2 )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH51 : ((-INT_MAX) <= N_2)) (PreH52 : (N_2 <= INT_MAX)) (PreH53 : (1 <= D_2)) (PreH54 : (D_2 <= INT_MAX)) (PreH55 : ((Zlength (CN_2)) = V_recompute)) (PreH56 : ((Zlength (CD_2)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : ((Znth (j) (CD_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD_2) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval_2 <> 0)) (PreH10 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH11 : (retval_2 = 1)) (PreH12 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH13 : ((-INT_MAX) <= P_2)) (PreH14 : (P_2 <= INT_MAX)) (PreH15 : (1 <= Q_2)) (PreH16 : (Q_2 <= INT_MAX)) (PreH17 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH18 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH19 : (((N_2 * Q ) + (P * D_2 ) ) <> 0)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH22 : (retval = 1)) (PreH23 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH24 : ((-INT_MAX) <= P)) (PreH25 : (P <= INT_MAX)) (PreH26 : (1 <= Q)) (PreH27 : (Q <= INT_MAX)) (PreH28 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH29 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH30 : (P = 0)) (PreH31 : (Q = 1)) (PreH32 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH33 : ((Znth j IB_recompute 0) = 0)) (PreH34 : (0 <= i)) (PreH35 : (i < R_recompute)) (PreH36 : (0 <= j)) (PreH37 : (j < V_recompute)) (PreH38 : (0 <= R_recompute)) (PreH39 : (R_recompute <= 16)) (PreH40 : (0 <= V_recompute)) (PreH41 : (V_recompute <= 24)) (PreH42 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH43 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH44 : ((Zlength (RN_recompute)) = R_recompute)) (PreH45 : ((Zlength (RD_recompute)) = R_recompute)) (PreH46 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH47 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH48 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH49 : (Forall (Z.le (1)) AD_recompute )) (PreH50 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH51 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH52 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH53 : (Forall (Z.le (1)) RD_recompute )) (PreH54 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH55 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH56 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH57 : (Forall (Z.le (1)) CD_2 )) (PreH58 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH59 : ((-INT_MAX) <= N_2)) (PreH60 : (N_2 <= INT_MAX)) (PreH61 : (1 <= D_2)) (PreH62 : (D_2 <= INT_MAX)) (PreH63 : ((Zlength (CN_2)) = V_recompute)) (PreH64 : ((Zlength (CD_2)) = V_recompute)) (PreH65 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH66 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= P_2) ”
  &&  “ (P_2 <= INT_MAX) ”
  &&  “ (1 <= Q_2) ”
  &&  “ (Q_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) P_2 Q_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_6_3_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH11 : (P_2 = 0)) (PreH12 : (Q_2 = 1)) (PreH13 : (retval <> 0)) (PreH14 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH15 : (retval = 1)) (PreH16 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH17 : ((-INT_MAX) <= P)) (PreH18 : (P <= INT_MAX)) (PreH19 : (1 <= Q)) (PreH20 : (Q <= INT_MAX)) (PreH21 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH22 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH23 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) <> 0)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH49 : (Forall (Z.le (1)) CD_2 )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH51 : ((-INT_MAX) <= N_2)) (PreH52 : (N_2 <= INT_MAX)) (PreH53 : (1 <= D_2)) (PreH54 : (D_2 <= INT_MAX)) (PreH55 : ((Zlength (CN_2)) = V_recompute)) (PreH56 : ((Zlength (CD_2)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : ((Znth (j) (CD_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD_2) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval_2 <> 0)) (PreH10 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH11 : (retval_2 = 1)) (PreH12 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH13 : ((-INT_MAX) <= P_2)) (PreH14 : (P_2 <= INT_MAX)) (PreH15 : (1 <= Q_2)) (PreH16 : (Q_2 <= INT_MAX)) (PreH17 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH18 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH19 : (P_2 = 0)) (PreH20 : (Q_2 = 1)) (PreH21 : (retval <> 0)) (PreH22 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH23 : (retval = 1)) (PreH24 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH25 : ((-INT_MAX) <= P)) (PreH26 : (P <= INT_MAX)) (PreH27 : (1 <= Q)) (PreH28 : (Q <= INT_MAX)) (PreH29 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH30 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH31 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) <> 0)) (PreH32 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH33 : ((Znth j IB_recompute 0) = 0)) (PreH34 : (0 <= i)) (PreH35 : (i < R_recompute)) (PreH36 : (0 <= j)) (PreH37 : (j < V_recompute)) (PreH38 : (0 <= R_recompute)) (PreH39 : (R_recompute <= 16)) (PreH40 : (0 <= V_recompute)) (PreH41 : (V_recompute <= 24)) (PreH42 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH43 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH44 : ((Zlength (RN_recompute)) = R_recompute)) (PreH45 : ((Zlength (RD_recompute)) = R_recompute)) (PreH46 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH47 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH48 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH49 : (Forall (Z.le (1)) AD_recompute )) (PreH50 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH51 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH52 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH53 : (Forall (Z.le (1)) RD_recompute )) (PreH54 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH55 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH56 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH57 : (Forall (Z.le (1)) CD_2 )) (PreH58 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH59 : ((-INT_MAX) <= N_2)) (PreH60 : (N_2 <= INT_MAX)) (PreH61 : (1 <= D_2)) (PreH62 : (D_2 <= INT_MAX)) (PreH63 : ((Zlength (CN_2)) = V_recompute)) (PreH64 : ((Zlength (CD_2)) = V_recompute)) (PreH65 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH66 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= P_2) ”
  &&  “ (P_2 <= INT_MAX) ”
  &&  “ (1 <= Q_2) ”
  &&  “ (Q_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) P_2 Q_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_6_4_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH3 : (retval_2 = 1)) (PreH4 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH5 : ((-INT_MAX) <= P_2)) (PreH6 : (P_2 <= INT_MAX)) (PreH7 : (1 <= Q_2)) (PreH8 : (Q_2 <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH10 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH11 : (((N_2 * Q ) + (P * D_2 ) ) <> 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH22 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) <> 0)) (PreH23 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH24 : ((Znth j IB_recompute 0) = 0)) (PreH25 : (0 <= i)) (PreH26 : (i < R_recompute)) (PreH27 : (0 <= j)) (PreH28 : (j < V_recompute)) (PreH29 : (0 <= R_recompute)) (PreH30 : (R_recompute <= 16)) (PreH31 : (0 <= V_recompute)) (PreH32 : (V_recompute <= 24)) (PreH33 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH34 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (RN_recompute)) = R_recompute)) (PreH36 : ((Zlength (RD_recompute)) = R_recompute)) (PreH37 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH38 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH40 : (Forall (Z.le (1)) AD_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH42 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH44 : (Forall (Z.le (1)) RD_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH46 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH47 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH48 : (Forall (Z.le (1)) CD_2 )) (PreH49 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH50 : ((-INT_MAX) <= N_2)) (PreH51 : (N_2 <= INT_MAX)) (PreH52 : (1 <= D_2)) (PreH53 : (D_2 <= INT_MAX)) (PreH54 : ((Zlength (CN_2)) = V_recompute)) (PreH55 : ((Zlength (CD_2)) = V_recompute)) (PreH56 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH57 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> P_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> Q_2)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (P_2: Z) (Q_2: Z) (retval_2: Z) (PreH1 : ((Znth (j) (CD_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD_2) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval_2 <> 0)) (PreH10 : (retval_2 = (simplex_rat_add_flag (N_2) (D_2) (P) (Q)))) (PreH11 : (retval_2 = 1)) (PreH12 : (simplex_rat_add_result N_2 D_2 P Q P_2 Q_2 )) (PreH13 : ((-INT_MAX) <= P_2)) (PreH14 : (P_2 <= INT_MAX)) (PreH15 : (1 <= Q_2)) (PreH16 : (Q_2 <= INT_MAX)) (PreH17 : ((Zgcd ((Zabs (P_2))) (Q_2)) = 1)) (PreH18 : ((((N_2 * Q ) + (P * D_2 ) ) * Q_2 ) = (P_2 * (D_2 * Q ) ))) (PreH19 : (((N_2 * Q ) + (P * D_2 ) ) <> 0)) (PreH20 : (retval <> 0)) (PreH21 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN_2) (0))) ((Znth (j) (CD_2) (0)))))) (PreH22 : (retval = 1)) (PreH23 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN_2) (0)) (Znth (j) (CD_2) (0)) P Q )) (PreH24 : ((-INT_MAX) <= P)) (PreH25 : (P <= INT_MAX)) (PreH26 : (1 <= Q)) (PreH27 : (Q <= INT_MAX)) (PreH28 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH29 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD_2) (0)) ) ))) (PreH30 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN_2) (0)) ) <> 0)) (PreH31 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH32 : ((Znth j IB_recompute 0) = 0)) (PreH33 : (0 <= i)) (PreH34 : (i < R_recompute)) (PreH35 : (0 <= j)) (PreH36 : (j < V_recompute)) (PreH37 : (0 <= R_recompute)) (PreH38 : (R_recompute <= 16)) (PreH39 : (0 <= V_recompute)) (PreH40 : (V_recompute <= 24)) (PreH41 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH42 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH43 : ((Zlength (RN_recompute)) = R_recompute)) (PreH44 : ((Zlength (RD_recompute)) = R_recompute)) (PreH45 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH46 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH47 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH48 : (Forall (Z.le (1)) AD_recompute )) (PreH49 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH50 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH51 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH52 : (Forall (Z.le (1)) RD_recompute )) (PreH53 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH54 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH55 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH56 : (Forall (Z.le (1)) CD_2 )) (PreH57 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH58 : ((-INT_MAX) <= N_2)) (PreH59 : (N_2 <= INT_MAX)) (PreH60 : (1 <= D_2)) (PreH61 : (D_2 <= INT_MAX)) (PreH62 : ((Zlength (CN_2)) = V_recompute)) (PreH63 : ((Zlength (CD_2)) = V_recompute)) (PreH64 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH65 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= P_2) ”
  &&  “ (P_2 <= INT_MAX) ”
  &&  “ (1 <= Q_2) ”
  &&  “ (Q_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) P_2 Q_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_6_5_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (PreH1 : ((Znth j IB_recompute 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j < V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH25 : (Forall (Z.le (1)) CD_2 )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH27 : ((-INT_MAX) <= N_2)) (PreH28 : (N_2 <= INT_MAX)) (PreH29 : (1 <= D_2)) (PreH30 : (D_2 <= INT_MAX)) (PreH31 : ((Zlength (CN_2)) = V_recompute)) (PreH32 : ((Zlength (CD_2)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D_2)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (PreH1 : ((Znth (j) (CD_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD_2) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : ((Znth j IB_recompute 0) <> 0)) (PreH10 : (0 <= i)) (PreH11 : (i < R_recompute)) (PreH12 : (0 <= j)) (PreH13 : (j < V_recompute)) (PreH14 : (0 <= R_recompute)) (PreH15 : (R_recompute <= 16)) (PreH16 : (0 <= V_recompute)) (PreH17 : (V_recompute <= 24)) (PreH18 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH19 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH20 : ((Zlength (RN_recompute)) = R_recompute)) (PreH21 : ((Zlength (RD_recompute)) = R_recompute)) (PreH22 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH23 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH24 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH25 : (Forall (Z.le (1)) AD_recompute )) (PreH26 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH27 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH28 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH29 : (Forall (Z.le (1)) RD_recompute )) (PreH30 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH31 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH32 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH33 : (Forall (Z.le (1)) CD_2 )) (PreH34 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH35 : ((-INT_MAX) <= N_2)) (PreH36 : (N_2 <= INT_MAX)) (PreH37 : (1 <= D_2)) (PreH38 : (D_2 <= INT_MAX)) (PreH39 : ((Zlength (CN_2)) = V_recompute)) (PreH40 : ((Zlength (CD_2)) = V_recompute)) (PreH41 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH42 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N_2) ”
  &&  “ (N_2 <= INT_MAX) ”
  &&  “ (1 <= D_2) ”
  &&  “ (D_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N_2 D_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_6_6_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (PreH1 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) = 0)) (PreH2 : ((Znth j IB_recompute 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < R_recompute)) (PreH5 : (0 <= j)) (PreH6 : (j < V_recompute)) (PreH7 : (0 <= R_recompute)) (PreH8 : (R_recompute <= 16)) (PreH9 : (0 <= V_recompute)) (PreH10 : (V_recompute <= 24)) (PreH11 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH13 : ((Zlength (RN_recompute)) = R_recompute)) (PreH14 : ((Zlength (RD_recompute)) = R_recompute)) (PreH15 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH16 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH18 : (Forall (Z.le (1)) AD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH21 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH22 : (Forall (Z.le (1)) RD_recompute )) (PreH23 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH24 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH25 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH26 : (Forall (Z.le (1)) CD_2 )) (PreH27 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH28 : ((-INT_MAX) <= N_2)) (PreH29 : (N_2 <= INT_MAX)) (PreH30 : (1 <= D_2)) (PreH31 : (D_2 <= INT_MAX)) (PreH32 : ((Zlength (CN_2)) = V_recompute)) (PreH33 : ((Zlength (CD_2)) = V_recompute)) (PreH34 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH35 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D_2)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N D ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N_2: Z) (D_2: Z) (i: Z) (j: Z) (PreH1 : ((Znth (j) (CD_2) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN_2) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD_2) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN_2) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) = 0)) (PreH10 : ((Znth j IB_recompute 0) = 0)) (PreH11 : (0 <= i)) (PreH12 : (i < R_recompute)) (PreH13 : (0 <= j)) (PreH14 : (j < V_recompute)) (PreH15 : (0 <= R_recompute)) (PreH16 : (R_recompute <= 16)) (PreH17 : (0 <= V_recompute)) (PreH18 : (V_recompute <= 24)) (PreH19 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH20 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH21 : ((Zlength (RN_recompute)) = R_recompute)) (PreH22 : ((Zlength (RD_recompute)) = R_recompute)) (PreH23 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH24 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH25 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH26 : (Forall (Z.le (1)) AD_recompute )) (PreH27 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH28 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH29 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH30 : (Forall (Z.le (1)) RD_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH32 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH33 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH34 : (Forall (Z.le (1)) CD_2 )) (PreH35 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH36 : ((-INT_MAX) <= N_2)) (PreH37 : (N_2 <= INT_MAX)) (PreH38 : (1 <= D_2)) (PreH39 : (D_2 <= INT_MAX)) (PreH40 : ((Zlength (CN_2)) = V_recompute)) (PreH41 : ((Zlength (CD_2)) = V_recompute)) (PreH42 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH43 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN_2) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD_2) (0)))
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N_2) ”
  &&  “ (N_2 <= INT_MAX) ”
  &&  “ (1 <= D_2) ”
  &&  “ (D_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i (j + 1 ) N_2 D_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_entail_wit_7_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (D_2: Z) (N_2: Z) (CD_2: (@list Z)) (CN_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= V_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j <= V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH25 : (Forall (Z.le (1)) CD_2 )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH27 : ((-INT_MAX) <= N_2)) (PreH28 : (N_2 <= INT_MAX)) (PreH29 : (1 <= D_2)) (PreH30 : (D_2 <= INT_MAX)) (PreH31 : ((Zlength (CN_2)) = V_recompute)) (PreH32 : ((Zlength (CD_2)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N_2)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D_2)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (D: Z) (N: Z) (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i V_recompute N D ) ”
  &&  ((( &( "j" ) )) # Int  |-> V_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (((&((S_recompute)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (Znth (i) (B_recompute) (0)))
  **  (IntArray.missing_i &((S_recompute)  # "SxState" ->ₛ "basic") i 0 R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD (Znth (i) (B_recompute) (0)) )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth (i) (B_recompute) (0))) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth (i) (B_recompute) (0))) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (D_2: Z) (N_2: Z) (CD_2: (@list Z)) (CN_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= V_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i < R_recompute)) (PreH4 : (0 <= j)) (PreH5 : (j <= V_recompute)) (PreH6 : (0 <= R_recompute)) (PreH7 : (R_recompute <= 16)) (PreH8 : (0 <= V_recompute)) (PreH9 : (V_recompute <= 24)) (PreH10 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (RN_recompute)) = R_recompute)) (PreH13 : ((Zlength (RD_recompute)) = R_recompute)) (PreH14 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH15 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH17 : (Forall (Z.le (1)) AD_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH19 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH21 : (Forall (Z.le (1)) RD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH25 : (Forall (Z.le (1)) CD_2 )) (PreH26 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH27 : ((-INT_MAX) <= N_2)) (PreH28 : (N_2 <= INT_MAX)) (PreH29 : (1 <= D_2)) (PreH30 : (D_2 <= INT_MAX)) (PreH31 : ((Zlength (CN_2)) = V_recompute)) (PreH32 : ((Zlength (CD_2)) = V_recompute)) (PreH33 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH34 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i j N_2 D_2 )),
  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN_2 CD_2 )
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ ((Znth (i) (B_recompute) (0)) = (Znth i B_recompute 0)) ”
  &&  “ (j = V_recompute) ”
  &&  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N_2) ”
  &&  “ (N_2 <= INT_MAX) ”
  &&  “ (1 <= D_2) ”
  &&  “ (D_2 <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i V_recompute N_2 D_2 ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD (Znth (i) (B_recompute) (0)) )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth (i) (B_recompute) (0))) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth (i) (B_recompute) (0))) (CD) (0)))
).

Definition sx_recompute_entail_wit_8_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N: Z) (D: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < R_recompute)) (PreH3 : (0 <= V_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH23 : (Forall (Z.le (1)) CD_2 )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH25 : ((-INT_MAX) <= N)) (PreH26 : (N <= INT_MAX)) (PreH27 : (1 <= D)) (PreH28 : (D <= INT_MAX)) (PreH29 : ((Zlength (CN_2)) = V_recompute)) (PreH30 : ((Zlength (CD_2)) = V_recompute)) (PreH31 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH32 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i V_recompute N D )),
  ((( &( "j" ) )) # Int  |-> V_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (((&((S_recompute)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (Znth (i) (B_recompute) (0)))
  **  (IntArray.missing_i &((S_recompute)  # "SxState" ->ₛ "basic") i 0 R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 (Znth (i) (B_recompute) (0)) )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute (i + 1 ) V_recompute 1 CN CD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (N: Z) (D: Z) (i: Z) (PreH1 : (D <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : ((Znth (i) (B_recompute) (0)) <= INT_MAX)) (PreH4 : (D >= INT_MIN)) (PreH5 : (N >= INT_MIN)) (PreH6 : ((Znth (i) (B_recompute) (0)) >= INT_MIN)) (PreH7 : (0 <= i)) (PreH8 : (i < R_recompute)) (PreH9 : (0 <= V_recompute)) (PreH10 : (0 <= R_recompute)) (PreH11 : (R_recompute <= 16)) (PreH12 : (0 <= V_recompute)) (PreH13 : (V_recompute <= 24)) (PreH14 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH15 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH16 : ((Zlength (RN_recompute)) = R_recompute)) (PreH17 : ((Zlength (RD_recompute)) = R_recompute)) (PreH18 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < R_recompute)) -> ((0 <= (Znth (k_2) (B_recompute) (0))) /\ ((Znth (k_2) (B_recompute) (0)) < V_recompute)))) (PreH19 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH21 : (Forall (Z.le (1)) AD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH24 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH25 : (Forall (Z.le (1)) RD_recompute )) (PreH26 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH27 : (Forall (Z.le ((-INT_MAX))) CN_2 )) (PreH28 : (Forall (Z.ge (INT_MAX)) CN_2 )) (PreH29 : (Forall (Z.le (1)) CD_2 )) (PreH30 : (Forall (Z.ge (INT_MAX)) CD_2 )) (PreH31 : ((-INT_MAX) <= N)) (PreH32 : (N <= INT_MAX)) (PreH33 : (1 <= D)) (PreH34 : (D <= INT_MAX)) (PreH35 : ((Zlength (CN_2)) = V_recompute)) (PreH36 : ((Zlength (CD_2)) = V_recompute)) (PreH37 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN_2 CD_2 )) (PreH38 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN_2 CD_2 RN_recompute RD_recompute i V_recompute N D )),
  (((&((S_recompute)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (Znth (i) (B_recompute) (0)))
  **  (IntArray.missing_i &((S_recompute)  # "SxState" ->ₛ "basic") i 0 R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values_except S_recompute V_recompute CN_2 CD_2 (Znth (i) (B_recompute) (0)) )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> N)
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + ((Znth (i) (B_recompute) (0)) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> D)
|--
  EX (CD: (@list Z)) (CN: (@list Z)),
  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute (i + 1 ) V_recompute 1 CN CD ) ”
  &&  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
).

Definition sx_recompute_return_wit_1_zero_rows :=
forall (S_zero_rows: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (i = 0)),
  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
|--
  “ (1 = 1) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
.

Definition sx_recompute_return_wit_2_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CD: (@list Z)) (CN: (@list Z)) (i: Z) (PreH1 : (i >= R_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i <= R_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN )) (PreH23 : (Forall (Z.le (1)) CD )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD )) (PreH25 : ((Zlength (CN)) = V_recompute)) (PreH26 : ((Zlength (CD)) = V_recompute)) (PreH27 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )),
  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 1 ON OD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (CD: (@list Z)) (CN: (@list Z)) (i: Z) (PreH1 : (i >= R_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i <= R_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN )) (PreH23 : (Forall (Z.le (1)) CD )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD )) (PreH25 : ((Zlength (CN)) = V_recompute)) (PreH26 : ((Zlength (CD)) = V_recompute)) (PreH27 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )),
  TT && emp 
|--
  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 1 CN CD ) ”
  &&  emp
).

Definition sx_recompute_return_wit_2_recompute_split_goal_1 :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (CD: (@list Z)) (CN: (@list Z)) (i: Z) (PreH1 : (i >= R_recompute)) (PreH2 : (0 <= i)) (PreH3 : (i <= R_recompute)) (PreH4 : (0 <= R_recompute)) (PreH5 : (R_recompute <= 16)) (PreH6 : (0 <= V_recompute)) (PreH7 : (V_recompute <= 24)) (PreH8 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (RN_recompute)) = R_recompute)) (PreH11 : ((Zlength (RD_recompute)) = R_recompute)) (PreH12 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH13 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH14 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH15 : (Forall (Z.le (1)) AD_recompute )) (PreH16 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH17 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH18 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH19 : (Forall (Z.le (1)) RD_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH21 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH22 : (Forall (Z.ge (INT_MAX)) CN )) (PreH23 : (Forall (Z.le (1)) CD )) (PreH24 : (Forall (Z.ge (INT_MAX)) CD )) (PreH25 : ((Zlength (CN)) = V_recompute)) (PreH26 : ((Zlength (CD)) = V_recompute)) (PreH27 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )),
  (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 1 CN CD )
.

Definition sx_recompute_return_wit_3_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH6 : (retval = 1)) (PreH7 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH8 : ((-INT_MAX) <= P)) (PreH9 : (P <= INT_MAX)) (PreH10 : (1 <= Q)) (PreH11 : (Q <= INT_MAX)) (PreH12 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH13 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH14 : (P = 0)) (PreH15 : (Q = 1)) (PreH16 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH17 : ((Znth j IB_recompute 0) = 0)) (PreH18 : (0 <= i)) (PreH19 : (i < R_recompute)) (PreH20 : (0 <= j)) (PreH21 : (j < V_recompute)) (PreH22 : (0 <= R_recompute)) (PreH23 : (R_recompute <= 16)) (PreH24 : (0 <= V_recompute)) (PreH25 : (V_recompute <= 24)) (PreH26 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH27 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH28 : ((Zlength (RN_recompute)) = R_recompute)) (PreH29 : ((Zlength (RD_recompute)) = R_recompute)) (PreH30 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH31 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH33 : (Forall (Z.le (1)) AD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH36 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH37 : (Forall (Z.le (1)) RD_recompute )) (PreH38 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH39 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH40 : (Forall (Z.ge (INT_MAX)) CN )) (PreH41 : (Forall (Z.le (1)) CD )) (PreH42 : (Forall (Z.ge (INT_MAX)) CD )) (PreH43 : ((-INT_MAX) <= N)) (PreH44 : (N <= INT_MAX)) (PreH45 : (1 <= D)) (PreH46 : (D <= INT_MAX)) (PreH47 : ((Zlength (CN)) = V_recompute)) (PreH48 : ((Zlength (CD)) = V_recompute)) (PreH49 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH50 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 0 ON OD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (j) (CD) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval_2 = 0)) (PreH10 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH11 : (retval_2 = 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH22 : (P = 0)) (PreH23 : (Q = 1)) (PreH24 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH25 : ((Znth j IB_recompute 0) = 0)) (PreH26 : (0 <= i)) (PreH27 : (i < R_recompute)) (PreH28 : (0 <= j)) (PreH29 : (j < V_recompute)) (PreH30 : (0 <= R_recompute)) (PreH31 : (R_recompute <= 16)) (PreH32 : (0 <= V_recompute)) (PreH33 : (V_recompute <= 24)) (PreH34 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH36 : ((Zlength (RN_recompute)) = R_recompute)) (PreH37 : ((Zlength (RD_recompute)) = R_recompute)) (PreH38 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH39 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH40 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH41 : (Forall (Z.le (1)) AD_recompute )) (PreH42 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH43 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH44 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH45 : (Forall (Z.le (1)) RD_recompute )) (PreH46 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH47 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH48 : (Forall (Z.ge (INT_MAX)) CN )) (PreH49 : (Forall (Z.le (1)) CD )) (PreH50 : (Forall (Z.ge (INT_MAX)) CD )) (PreH51 : ((-INT_MAX) <= N)) (PreH52 : (N <= INT_MAX)) (PreH53 : (1 <= D)) (PreH54 : (D <= INT_MAX)) (PreH55 : ((Zlength (CN)) = V_recompute)) (PreH56 : ((Zlength (CD)) = V_recompute)) (PreH57 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH58 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 0 ON OD ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
).

Definition sx_recompute_return_wit_4_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH3 : (retval_2 = 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH6 : (retval = 1)) (PreH7 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH8 : ((-INT_MAX) <= P)) (PreH9 : (P <= INT_MAX)) (PreH10 : (1 <= Q)) (PreH11 : (Q <= INT_MAX)) (PreH12 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH13 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH14 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH15 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH16 : ((Znth j IB_recompute 0) = 0)) (PreH17 : (0 <= i)) (PreH18 : (i < R_recompute)) (PreH19 : (0 <= j)) (PreH20 : (j < V_recompute)) (PreH21 : (0 <= R_recompute)) (PreH22 : (R_recompute <= 16)) (PreH23 : (0 <= V_recompute)) (PreH24 : (V_recompute <= 24)) (PreH25 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH26 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH27 : ((Zlength (RN_recompute)) = R_recompute)) (PreH28 : ((Zlength (RD_recompute)) = R_recompute)) (PreH29 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH30 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH32 : (Forall (Z.le (1)) AD_recompute )) (PreH33 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH34 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH35 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH36 : (Forall (Z.le (1)) RD_recompute )) (PreH37 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH38 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH39 : (Forall (Z.ge (INT_MAX)) CN )) (PreH40 : (Forall (Z.le (1)) CD )) (PreH41 : (Forall (Z.ge (INT_MAX)) CD )) (PreH42 : ((-INT_MAX) <= N)) (PreH43 : (N <= INT_MAX)) (PreH44 : (1 <= D)) (PreH45 : (D <= INT_MAX)) (PreH46 : ((Zlength (CN)) = V_recompute)) (PreH47 : ((Zlength (CD)) = V_recompute)) (PreH48 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH49 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 0 ON OD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth (j) (CD) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval_2 = 0)) (PreH10 : (retval_2 = (simplex_rat_add_flag (N) (D) (P) (Q)))) (PreH11 : (retval_2 = 0)) (PreH12 : (retval <> 0)) (PreH13 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH14 : (retval = 1)) (PreH15 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH16 : ((-INT_MAX) <= P)) (PreH17 : (P <= INT_MAX)) (PreH18 : (1 <= Q)) (PreH19 : (Q <= INT_MAX)) (PreH20 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH21 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH22 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH23 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH24 : ((Znth j IB_recompute 0) = 0)) (PreH25 : (0 <= i)) (PreH26 : (i < R_recompute)) (PreH27 : (0 <= j)) (PreH28 : (j < V_recompute)) (PreH29 : (0 <= R_recompute)) (PreH30 : (R_recompute <= 16)) (PreH31 : (0 <= V_recompute)) (PreH32 : (V_recompute <= 24)) (PreH33 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH34 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH35 : ((Zlength (RN_recompute)) = R_recompute)) (PreH36 : ((Zlength (RD_recompute)) = R_recompute)) (PreH37 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH38 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH40 : (Forall (Z.le (1)) AD_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH42 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH44 : (Forall (Z.le (1)) RD_recompute )) (PreH45 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH46 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH47 : (Forall (Z.ge (INT_MAX)) CN )) (PreH48 : (Forall (Z.le (1)) CD )) (PreH49 : (Forall (Z.ge (INT_MAX)) CD )) (PreH50 : ((-INT_MAX) <= N)) (PreH51 : (N <= INT_MAX)) (PreH52 : (1 <= D)) (PreH53 : (D <= INT_MAX)) (PreH54 : ((Zlength (CN)) = V_recompute)) (PreH55 : ((Zlength (CD)) = V_recompute)) (PreH56 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH57 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 0 ON OD ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
).

Definition sx_recompute_return_wit_5_recompute :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 0)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH5 : ((Znth j IB_recompute 0) = 0)) (PreH6 : (0 <= i)) (PreH7 : (i < R_recompute)) (PreH8 : (0 <= j)) (PreH9 : (j < V_recompute)) (PreH10 : (0 <= R_recompute)) (PreH11 : (R_recompute <= 16)) (PreH12 : (0 <= V_recompute)) (PreH13 : (V_recompute <= 24)) (PreH14 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH15 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH16 : ((Zlength (RN_recompute)) = R_recompute)) (PreH17 : ((Zlength (RD_recompute)) = R_recompute)) (PreH18 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH19 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH20 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH21 : (Forall (Z.le (1)) AD_recompute )) (PreH22 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH23 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH24 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH25 : (Forall (Z.le (1)) RD_recompute )) (PreH26 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH27 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH28 : (Forall (Z.ge (INT_MAX)) CN )) (PreH29 : (Forall (Z.le (1)) CD )) (PreH30 : (Forall (Z.ge (INT_MAX)) CD )) (PreH31 : ((-INT_MAX) <= N)) (PreH32 : (N <= INT_MAX)) (PreH33 : (1 <= D)) (PreH34 : (D <= INT_MAX)) (PreH35 : ((Zlength (CN)) = V_recompute)) (PreH36 : ((Zlength (CD)) = V_recompute)) (PreH37 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH38 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 0 ON OD ) ”
  &&  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (retval: Z) (PreH1 : ((Znth (j) (CD) (0)) <= INT_MAX)) (PreH2 : ((Znth (j) (CN) (0)) <= INT_MAX)) (PreH3 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH4 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH5 : ((Znth (j) (CD) (0)) >= INT_MIN)) (PreH6 : ((Znth (j) (CN) (0)) >= INT_MIN)) (PreH7 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH8 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH9 : (retval = 0)) (PreH10 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH11 : (retval = 0)) (PreH12 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH13 : ((Znth j IB_recompute 0) = 0)) (PreH14 : (0 <= i)) (PreH15 : (i < R_recompute)) (PreH16 : (0 <= j)) (PreH17 : (j < V_recompute)) (PreH18 : (0 <= R_recompute)) (PreH19 : (R_recompute <= 16)) (PreH20 : (0 <= V_recompute)) (PreH21 : (V_recompute <= 24)) (PreH22 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH23 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (RN_recompute)) = R_recompute)) (PreH25 : ((Zlength (RD_recompute)) = R_recompute)) (PreH26 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH27 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH28 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH29 : (Forall (Z.le (1)) AD_recompute )) (PreH30 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH31 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH33 : (Forall (Z.le (1)) RD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH36 : (Forall (Z.ge (INT_MAX)) CN )) (PreH37 : (Forall (Z.le (1)) CD )) (PreH38 : (Forall (Z.ge (INT_MAX)) CD )) (PreH39 : ((-INT_MAX) <= N)) (PreH40 : (N <= INT_MAX)) (PreH41 : (1 <= D)) (PreH42 : (D <= INT_MAX)) (PreH43 : ((Zlength (CN)) = V_recompute)) (PreH44 : ((Zlength (CD)) = V_recompute)) (PreH45 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH46 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
|--
  EX (OD: (@list Z)) (ON: (@list Z)),
  “ (Forall (Z.le ((-INT_MAX))) ON ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) ON ) ”
  &&  “ (Forall (Z.le (1)) OD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) OD ) ”
  &&  “ ((Zlength (ON)) = V_recompute) ”
  &&  “ ((Zlength (OD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute R_recompute V_recompute 0 ON OD ) ”
  &&  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute ON OD )
).

Definition sx_recompute_partial_solve_wit_1_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < R_recompute)) (PreH3 : (0 <= R_recompute)) (PreH4 : (R_recompute <= 16)) (PreH5 : (0 <= V_recompute)) (PreH6 : (V_recompute <= 24)) (PreH7 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH8 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH9 : ((Zlength (RN_recompute)) = R_recompute)) (PreH10 : ((Zlength (RD_recompute)) = R_recompute)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH12 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH13 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH14 : (Forall (Z.le (1)) AD_recompute )) (PreH15 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH16 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH18 : (Forall (Z.le (1)) RD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH21 : (Forall (Z.ge (INT_MAX)) CN )) (PreH22 : (Forall (Z.le (1)) CD )) (PreH23 : (Forall (Z.ge (INT_MAX)) CD )) (PreH24 : ((Zlength (CN)) = V_recompute)) (PreH25 : ((Zlength (CD)) = V_recompute)) (PreH26 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )),
  (UndefStructPredSxRat ( &( "sum" ) ) )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  ((&(( &( "sum" ) )->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (i) (RD_recompute) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (i) (RN_recompute) (0)))
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs_except S_recompute R_recompute RN_recompute RD_recompute i )
  **  (simplex_recompute_matrix S_recompute R_recompute V_recompute AN_recompute AD_recompute )
  **  (simplex_recompute_values S_recompute V_recompute CN CD )
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
.

Definition sx_recompute_partial_solve_wit_2_recompute :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : (0 <= i)) (PreH2 : (i < R_recompute)) (PreH3 : (0 <= j)) (PreH4 : (j < V_recompute)) (PreH5 : (0 <= R_recompute)) (PreH6 : (R_recompute <= 16)) (PreH7 : (0 <= V_recompute)) (PreH8 : (V_recompute <= 24)) (PreH9 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH10 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH11 : ((Zlength (RN_recompute)) = R_recompute)) (PreH12 : ((Zlength (RD_recompute)) = R_recompute)) (PreH13 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH14 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH15 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH16 : (Forall (Z.le (1)) AD_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH18 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH20 : (Forall (Z.le (1)) RD_recompute )) (PreH21 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH22 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH23 : (Forall (Z.ge (INT_MAX)) CN )) (PreH24 : (Forall (Z.le (1)) CD )) (PreH25 : (Forall (Z.ge (INT_MAX)) CD )) (PreH26 : ((-INT_MAX) <= N)) (PreH27 : (N <= INT_MAX)) (PreH28 : (1 <= D)) (PreH29 : (D <= INT_MAX)) (PreH30 : ((Zlength (CN)) = V_recompute)) (PreH31 : ((Zlength (CD)) = V_recompute)) (PreH32 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH33 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= j) ”
  &&  “ (j < V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D ) ”
  &&  (((&((S_recompute)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> (Znth j IB_recompute 0))
  **  (IntArray.missing_i &((S_recompute)  # "SxState" ->ₛ "is_basic") j 0 V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
.

Definition sx_recompute_partial_solve_wit_3_recompute_pure :=
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH2 : ((Znth j IB_recompute 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < R_recompute)) (PreH5 : (0 <= j)) (PreH6 : (j < V_recompute)) (PreH7 : (0 <= R_recompute)) (PreH8 : (R_recompute <= 16)) (PreH9 : (0 <= V_recompute)) (PreH10 : (V_recompute <= 24)) (PreH11 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH13 : ((Zlength (RN_recompute)) = R_recompute)) (PreH14 : ((Zlength (RD_recompute)) = R_recompute)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH16 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH18 : (Forall (Z.le (1)) AD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH21 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH22 : (Forall (Z.le (1)) RD_recompute )) (PreH23 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH24 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH25 : (Forall (Z.ge (INT_MAX)) CN )) (PreH26 : (Forall (Z.le (1)) CD )) (PreH27 : (Forall (Z.ge (INT_MAX)) CD )) (PreH28 : ((-INT_MAX) <= N)) (PreH29 : (N <= INT_MAX)) (PreH30 : (1 <= D)) (PreH31 : (D <= INT_MAX)) (PreH32 : ((Zlength (CN)) = V_recompute)) (PreH33 : ((Zlength (CD)) = V_recompute)) (PreH34 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH35 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ ((Znth (j) (CD) (0)) <= INT_MAX) ”
  &&  “ (1 <= (Znth (j) (CD) (0))) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX) ”
  &&  “ (1 <= (Znth (((i * 24 ) + j )) (AD_recompute) (0))) ”
  &&  “ ((Znth (j) (CN) (0)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (Znth (j) (CN) (0))) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (Znth (((i * 24 ) + j )) (AN_recompute) (0))) ”
) \/
(
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : (D <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : ((Znth (j) (CD) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (CN) (0)) <= INT_MAX)) (PreH5 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH6 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH7 : (V_recompute <= INT_MAX)) (PreH8 : (R_recompute <= INT_MAX)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (D >= INT_MIN)) (PreH12 : (N >= INT_MIN)) (PreH13 : ((Znth (j) (CD) (0)) >= INT_MIN)) (PreH14 : ((Znth (j) (CN) (0)) >= INT_MIN)) (PreH15 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH16 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH17 : (V_recompute >= INT_MIN)) (PreH18 : (R_recompute >= INT_MIN)) (PreH19 : (j >= INT_MIN)) (PreH20 : (i >= INT_MIN)) (PreH21 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH22 : ((Znth j IB_recompute 0) = 0)) (PreH23 : (0 <= i)) (PreH24 : (i < R_recompute)) (PreH25 : (0 <= j)) (PreH26 : (j < V_recompute)) (PreH27 : (0 <= R_recompute)) (PreH28 : (R_recompute <= 16)) (PreH29 : (0 <= V_recompute)) (PreH30 : (V_recompute <= 24)) (PreH31 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH32 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH33 : ((Zlength (RN_recompute)) = R_recompute)) (PreH34 : ((Zlength (RD_recompute)) = R_recompute)) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH36 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH37 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH38 : (Forall (Z.le (1)) AD_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH40 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH42 : (Forall (Z.le (1)) RD_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH44 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH45 : (Forall (Z.ge (INT_MAX)) CN )) (PreH46 : (Forall (Z.le (1)) CD )) (PreH47 : (Forall (Z.ge (INT_MAX)) CD )) (PreH48 : ((-INT_MAX) <= N)) (PreH49 : (N <= INT_MAX)) (PreH50 : (1 <= D)) (PreH51 : (D <= INT_MAX)) (PreH52 : ((Zlength (CN)) = V_recompute)) (PreH53 : ((Zlength (CD)) = V_recompute)) (PreH54 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH55 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (1 <= (Znth (((i * 24 ) + j )) (AD_recompute) (0))) ”
  &&  “ (1 <= (Znth (j) (CD) (0))) ”
).

Definition sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_1 :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : (D <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : ((Znth (j) (CD) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (CN) (0)) <= INT_MAX)) (PreH5 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH6 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH7 : (V_recompute <= INT_MAX)) (PreH8 : (R_recompute <= INT_MAX)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (D >= INT_MIN)) (PreH12 : (N >= INT_MIN)) (PreH13 : ((Znth (j) (CD) (0)) >= INT_MIN)) (PreH14 : ((Znth (j) (CN) (0)) >= INT_MIN)) (PreH15 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH16 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH17 : (V_recompute >= INT_MIN)) (PreH18 : (R_recompute >= INT_MIN)) (PreH19 : (j >= INT_MIN)) (PreH20 : (i >= INT_MIN)) (PreH21 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH22 : ((Znth j IB_recompute 0) = 0)) (PreH23 : (0 <= i)) (PreH24 : (i < R_recompute)) (PreH25 : (0 <= j)) (PreH26 : (j < V_recompute)) (PreH27 : (0 <= R_recompute)) (PreH28 : (R_recompute <= 16)) (PreH29 : (0 <= V_recompute)) (PreH30 : (V_recompute <= 24)) (PreH31 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH32 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH33 : ((Zlength (RN_recompute)) = R_recompute)) (PreH34 : ((Zlength (RD_recompute)) = R_recompute)) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH36 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH37 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH38 : (Forall (Z.le (1)) AD_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH40 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH42 : (Forall (Z.le (1)) RD_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH44 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH45 : (Forall (Z.ge (INT_MAX)) CN )) (PreH46 : (Forall (Z.le (1)) CD )) (PreH47 : (Forall (Z.ge (INT_MAX)) CD )) (PreH48 : ((-INT_MAX) <= N)) (PreH49 : (N <= INT_MAX)) (PreH50 : (1 <= D)) (PreH51 : (D <= INT_MAX)) (PreH52 : ((Zlength (CN)) = V_recompute)) (PreH53 : ((Zlength (CD)) = V_recompute)) (PreH54 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH55 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (1 <= (Znth (((i * 24 ) + j )) (AD_recompute) (0))) ”
.

Definition sx_recompute_partial_solve_wit_3_recompute_pure_split_goal_2 :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : (D <= INT_MAX)) (PreH2 : (N <= INT_MAX)) (PreH3 : ((Znth (j) (CD) (0)) <= INT_MAX)) (PreH4 : ((Znth (j) (CN) (0)) <= INT_MAX)) (PreH5 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX)) (PreH6 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX)) (PreH7 : (V_recompute <= INT_MAX)) (PreH8 : (R_recompute <= INT_MAX)) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (D >= INT_MIN)) (PreH12 : (N >= INT_MIN)) (PreH13 : ((Znth (j) (CD) (0)) >= INT_MIN)) (PreH14 : ((Znth (j) (CN) (0)) >= INT_MIN)) (PreH15 : ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) >= INT_MIN)) (PreH16 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) >= INT_MIN)) (PreH17 : (V_recompute >= INT_MIN)) (PreH18 : (R_recompute >= INT_MIN)) (PreH19 : (j >= INT_MIN)) (PreH20 : (i >= INT_MIN)) (PreH21 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH22 : ((Znth j IB_recompute 0) = 0)) (PreH23 : (0 <= i)) (PreH24 : (i < R_recompute)) (PreH25 : (0 <= j)) (PreH26 : (j < V_recompute)) (PreH27 : (0 <= R_recompute)) (PreH28 : (R_recompute <= 16)) (PreH29 : (0 <= V_recompute)) (PreH30 : (V_recompute <= 24)) (PreH31 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH32 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH33 : ((Zlength (RN_recompute)) = R_recompute)) (PreH34 : ((Zlength (RD_recompute)) = R_recompute)) (PreH35 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH36 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH37 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH38 : (Forall (Z.le (1)) AD_recompute )) (PreH39 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH40 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH41 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH42 : (Forall (Z.le (1)) RD_recompute )) (PreH43 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH44 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH45 : (Forall (Z.ge (INT_MAX)) CN )) (PreH46 : (Forall (Z.le (1)) CD )) (PreH47 : (Forall (Z.ge (INT_MAX)) CD )) (PreH48 : ((-INT_MAX) <= N)) (PreH49 : (N <= INT_MAX)) (PreH50 : (1 <= D)) (PreH51 : (D <= INT_MAX)) (PreH52 : ((Zlength (CN)) = V_recompute)) (PreH53 : ((Zlength (CD)) = V_recompute)) (PreH54 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH55 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ (1 <= (Znth (j) (CD) (0))) ”
.

Definition sx_recompute_partial_solve_wit_3_recompute_aux :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (PreH1 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH2 : ((Znth j IB_recompute 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i < R_recompute)) (PreH5 : (0 <= j)) (PreH6 : (j < V_recompute)) (PreH7 : (0 <= R_recompute)) (PreH8 : (R_recompute <= 16)) (PreH9 : (0 <= V_recompute)) (PreH10 : (V_recompute <= 24)) (PreH11 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH12 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH13 : ((Zlength (RN_recompute)) = R_recompute)) (PreH14 : ((Zlength (RD_recompute)) = R_recompute)) (PreH15 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH16 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH17 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH18 : (Forall (Z.le (1)) AD_recompute )) (PreH19 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH20 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH21 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH22 : (Forall (Z.le (1)) RD_recompute )) (PreH23 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH24 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH25 : (Forall (Z.ge (INT_MAX)) CN )) (PreH26 : (Forall (Z.le (1)) CD )) (PreH27 : (Forall (Z.ge (INT_MAX)) CD )) (PreH28 : ((-INT_MAX) <= N)) (PreH29 : (N <= INT_MAX)) (PreH30 : (1 <= D)) (PreH31 : (D <= INT_MAX)) (PreH32 : ((Zlength (CN)) = V_recompute)) (PreH33 : ((Zlength (CD)) = V_recompute)) (PreH34 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH35 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
|--
  “ ((Znth (j) (CD) (0)) <= INT_MAX) ”
  &&  “ (1 <= (Znth (j) (CD) (0))) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) <= INT_MAX) ”
  &&  “ (1 <= (Znth (((i * 24 ) + j )) (AD_recompute) (0))) ”
  &&  “ ((Znth (j) (CN) (0)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (Znth (j) (CN) (0))) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (Znth (((i * 24 ) + j )) (AN_recompute) (0))) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0) ”
  &&  “ ((Znth j IB_recompute 0) = 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= j) ”
  &&  “ (j < V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D ) ”
  &&  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |->_)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |->_)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
.

Definition sx_recompute_partial_solve_wit_3_recompute := sx_recompute_partial_solve_wit_3_recompute_pure -> sx_recompute_partial_solve_wit_3_recompute_aux.

Definition sx_recompute_partial_solve_wit_4_recompute_pure :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 1)) (PreH4 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH5 : ((-INT_MAX) <= P)) (PreH6 : (P <= INT_MAX)) (PreH7 : (1 <= Q)) (PreH8 : (Q <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH10 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH11 : (P = 0)) (PreH12 : (Q = 1)) (PreH13 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH14 : ((Znth j IB_recompute 0) = 0)) (PreH15 : (0 <= i)) (PreH16 : (i < R_recompute)) (PreH17 : (0 <= j)) (PreH18 : (j < V_recompute)) (PreH19 : (0 <= R_recompute)) (PreH20 : (R_recompute <= 16)) (PreH21 : (0 <= V_recompute)) (PreH22 : (V_recompute <= 24)) (PreH23 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH25 : ((Zlength (RN_recompute)) = R_recompute)) (PreH26 : ((Zlength (RD_recompute)) = R_recompute)) (PreH27 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH28 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH29 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH30 : (Forall (Z.le (1)) AD_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH32 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH33 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH34 : (Forall (Z.le (1)) RD_recompute )) (PreH35 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH36 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH37 : (Forall (Z.ge (INT_MAX)) CN )) (PreH38 : (Forall (Z.le (1)) CD )) (PreH39 : (Forall (Z.ge (INT_MAX)) CD )) (PreH40 : ((-INT_MAX) <= N)) (PreH41 : (N <= INT_MAX)) (PreH42 : (1 <= D)) (PreH43 : (D <= INT_MAX)) (PreH44 : ((Zlength (CN)) = V_recompute)) (PreH45 : ((Zlength (CD)) = V_recompute)) (PreH46 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH47 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ (( &( "sum" ) ) = ( &( "sum" ) )) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ ((-INT_MAX) <= P) ”
  &&  “ (P <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ (1 <= Q) ”
  &&  “ (Q <= INT_MAX) ”
.

Definition sx_recompute_partial_solve_wit_4_recompute_aux :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 1)) (PreH4 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH5 : ((-INT_MAX) <= P)) (PreH6 : (P <= INT_MAX)) (PreH7 : (1 <= Q)) (PreH8 : (Q <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH10 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH11 : (P = 0)) (PreH12 : (Q = 1)) (PreH13 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH14 : ((Znth j IB_recompute 0) = 0)) (PreH15 : (0 <= i)) (PreH16 : (i < R_recompute)) (PreH17 : (0 <= j)) (PreH18 : (j < V_recompute)) (PreH19 : (0 <= R_recompute)) (PreH20 : (R_recompute <= 16)) (PreH21 : (0 <= V_recompute)) (PreH22 : (V_recompute <= 24)) (PreH23 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH25 : ((Zlength (RN_recompute)) = R_recompute)) (PreH26 : ((Zlength (RD_recompute)) = R_recompute)) (PreH27 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH28 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH29 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH30 : (Forall (Z.le (1)) AD_recompute )) (PreH31 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH32 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH33 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH34 : (Forall (Z.le (1)) RD_recompute )) (PreH35 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH36 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH37 : (Forall (Z.ge (INT_MAX)) CN )) (PreH38 : (Forall (Z.le (1)) CD )) (PreH39 : (Forall (Z.ge (INT_MAX)) CD )) (PreH40 : ((-INT_MAX) <= N)) (PreH41 : (N <= INT_MAX)) (PreH42 : (1 <= D)) (PreH43 : (D <= INT_MAX)) (PreH44 : ((Zlength (CN)) = V_recompute)) (PreH45 : ((Zlength (CD)) = V_recompute)) (PreH46 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH47 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ (( &( "sum" ) ) = ( &( "sum" ) )) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ ((-INT_MAX) <= P) ”
  &&  “ (P <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ (1 <= Q) ”
  &&  “ (Q <= INT_MAX) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0))))) ”
  &&  “ (retval = 1) ”
  &&  “ (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q ) ”
  &&  “ ((-INT_MAX) <= P) ”
  &&  “ (P <= INT_MAX) ”
  &&  “ (1 <= Q) ”
  &&  “ (Q <= INT_MAX) ”
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ”
  &&  “ ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) )) ”
  &&  “ (P = 0) ”
  &&  “ (Q = 1) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0) ”
  &&  “ ((Znth j IB_recompute 0) = 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= j) ”
  &&  “ (j < V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D ) ”
  &&  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
.

Definition sx_recompute_partial_solve_wit_4_recompute := sx_recompute_partial_solve_wit_4_recompute_pure -> sx_recompute_partial_solve_wit_4_recompute_aux.

Definition sx_recompute_partial_solve_wit_5_recompute_pure :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 1)) (PreH4 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH5 : ((-INT_MAX) <= P)) (PreH6 : (P <= INT_MAX)) (PreH7 : (1 <= Q)) (PreH8 : (Q <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH10 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH11 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH12 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH13 : ((Znth j IB_recompute 0) = 0)) (PreH14 : (0 <= i)) (PreH15 : (i < R_recompute)) (PreH16 : (0 <= j)) (PreH17 : (j < V_recompute)) (PreH18 : (0 <= R_recompute)) (PreH19 : (R_recompute <= 16)) (PreH20 : (0 <= V_recompute)) (PreH21 : (V_recompute <= 24)) (PreH22 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH23 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (RN_recompute)) = R_recompute)) (PreH25 : ((Zlength (RD_recompute)) = R_recompute)) (PreH26 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH27 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH28 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH29 : (Forall (Z.le (1)) AD_recompute )) (PreH30 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH31 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH33 : (Forall (Z.le (1)) RD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH36 : (Forall (Z.ge (INT_MAX)) CN )) (PreH37 : (Forall (Z.le (1)) CD )) (PreH38 : (Forall (Z.ge (INT_MAX)) CD )) (PreH39 : ((-INT_MAX) <= N)) (PreH40 : (N <= INT_MAX)) (PreH41 : (1 <= D)) (PreH42 : (D <= INT_MAX)) (PreH43 : ((Zlength (CN)) = V_recompute)) (PreH44 : ((Zlength (CD)) = V_recompute)) (PreH45 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH46 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((( &( "s" ) )) # Ptr  |-> S_recompute)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ (( &( "sum" ) ) = ( &( "sum" ) )) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ ((-INT_MAX) <= P) ”
  &&  “ (P <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ (1 <= Q) ”
  &&  “ (Q <= INT_MAX) ”
.

Definition sx_recompute_partial_solve_wit_5_recompute_aux :=
forall (VD_recompute: (@list Z)) (VN_recompute: (@list Z)) (B_recompute: (@list Z)) (RD_recompute: (@list Z)) (RN_recompute: (@list Z)) (AD_recompute: (@list Z)) (AN_recompute: (@list Z)) (IB_recompute: (@list Z)) (V_recompute: Z) (R_recompute: Z) (S_recompute: Z) (CN: (@list Z)) (CD: (@list Z)) (N: Z) (D: Z) (i: Z) (j: Z) (P: Z) (Q: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0)))))) (PreH3 : (retval = 1)) (PreH4 : (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q )) (PreH5 : ((-INT_MAX) <= P)) (PreH6 : (P <= INT_MAX)) (PreH7 : (1 <= Q)) (PreH8 : (Q <= INT_MAX)) (PreH9 : ((Zgcd ((Zabs (P))) (Q)) = 1)) (PreH10 : ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) ))) (PreH11 : (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0)) (PreH12 : ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0)) (PreH13 : ((Znth j IB_recompute 0) = 0)) (PreH14 : (0 <= i)) (PreH15 : (i < R_recompute)) (PreH16 : (0 <= j)) (PreH17 : (j < V_recompute)) (PreH18 : (0 <= R_recompute)) (PreH19 : (R_recompute <= 16)) (PreH20 : (0 <= V_recompute)) (PreH21 : (V_recompute <= 24)) (PreH22 : ((Zlength (AN_recompute)) = (R_recompute * 24 ))) (PreH23 : ((Zlength (AD_recompute)) = (R_recompute * 24 ))) (PreH24 : ((Zlength (RN_recompute)) = R_recompute)) (PreH25 : ((Zlength (RD_recompute)) = R_recompute)) (PreH26 : forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute)))) (PreH27 : (Forall (Z.le ((-INT_MAX))) AN_recompute )) (PreH28 : (Forall (Z.ge (INT_MAX)) AN_recompute )) (PreH29 : (Forall (Z.le (1)) AD_recompute )) (PreH30 : (Forall (Z.ge (INT_MAX)) AD_recompute )) (PreH31 : (Forall (Z.le ((-INT_MAX))) RN_recompute )) (PreH32 : (Forall (Z.ge (INT_MAX)) RN_recompute )) (PreH33 : (Forall (Z.le (1)) RD_recompute )) (PreH34 : (Forall (Z.ge (INT_MAX)) RD_recompute )) (PreH35 : (Forall (Z.le ((-INT_MAX))) CN )) (PreH36 : (Forall (Z.ge (INT_MAX)) CN )) (PreH37 : (Forall (Z.le (1)) CD )) (PreH38 : (Forall (Z.ge (INT_MAX)) CD )) (PreH39 : ((-INT_MAX) <= N)) (PreH40 : (N <= INT_MAX)) (PreH41 : (1 <= D)) (PreH42 : (D <= INT_MAX)) (PreH43 : ((Zlength (CN)) = V_recompute)) (PreH44 : ((Zlength (CD)) = V_recompute)) (PreH45 : (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD )) (PreH46 : (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D )),
  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
  **  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
|--
  “ (( &( "sum" ) ) = ( &( "sum" ) )) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ ((-INT_MAX) <= P) ”
  &&  “ (P <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ (1 <= Q) ”
  &&  “ (Q <= INT_MAX) ”
  &&  “ (retval <> 0) ”
  &&  “ (retval = (simplex_rat_mul_flag ((Znth (((i * 24 ) + j )) (AN_recompute) (0))) ((Znth (((i * 24 ) + j )) (AD_recompute) (0))) ((Znth (j) (CN) (0))) ((Znth (j) (CD) (0))))) ”
  &&  “ (retval = 1) ”
  &&  “ (simplex_rat_mul_result (Znth (((i * 24 ) + j )) (AN_recompute) (0)) (Znth (((i * 24 ) + j )) (AD_recompute) (0)) (Znth (j) (CN) (0)) (Znth (j) (CD) (0)) P Q ) ”
  &&  “ ((-INT_MAX) <= P) ”
  &&  “ (P <= INT_MAX) ”
  &&  “ (1 <= Q) ”
  &&  “ (Q <= INT_MAX) ”
  &&  “ ((Zgcd ((Zabs (P))) (Q)) = 1) ”
  &&  “ ((((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) * Q ) = (P * ((Znth (((i * 24 ) + j )) (AD_recompute) (0)) * (Znth (j) (CD) (0)) ) )) ”
  &&  “ (((Znth (((i * 24 ) + j )) (AN_recompute) (0)) * (Znth (j) (CN) (0)) ) <> 0) ”
  &&  “ ((Znth (((i * 24 ) + j )) (AN_recompute) (0)) <> 0) ”
  &&  “ ((Znth j IB_recompute 0) = 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < R_recompute) ”
  &&  “ (0 <= j) ”
  &&  “ (j < V_recompute) ”
  &&  “ (0 <= R_recompute) ”
  &&  “ (R_recompute <= 16) ”
  &&  “ (0 <= V_recompute) ”
  &&  “ (V_recompute <= 24) ”
  &&  “ ((Zlength (AN_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (AD_recompute)) = (R_recompute * 24 )) ”
  &&  “ ((Zlength (RN_recompute)) = R_recompute) ”
  &&  “ ((Zlength (RD_recompute)) = R_recompute) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < R_recompute)) -> ((0 <= (Znth (k) (B_recompute) (0))) /\ ((Znth (k) (B_recompute) (0)) < V_recompute))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) AN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AN_recompute ) ”
  &&  “ (Forall (Z.le (1)) AD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) AD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) RN_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RN_recompute ) ”
  &&  “ (Forall (Z.le (1)) RD_recompute ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) RD_recompute ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CN ) ”
  &&  “ (Forall (Z.le (1)) CD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CD ) ”
  &&  “ ((-INT_MAX) <= N) ”
  &&  “ (N <= INT_MAX) ”
  &&  “ (1 <= D) ”
  &&  “ (D <= INT_MAX) ”
  &&  “ ((Zlength (CN)) = V_recompute) ”
  &&  “ ((Zlength (CD)) = V_recompute) ”
  &&  “ (simplex_recompute_prefix IB_recompute AN_recompute AD_recompute RN_recompute RD_recompute B_recompute VN_recompute VD_recompute i V_recompute 1 CN CD ) ”
  &&  “ (simplex_recompute_sum IB_recompute AN_recompute AD_recompute CN CD RN_recompute RD_recompute i j N D ) ”
  &&  ((&(( &( "sum" ) )->ₛ "num")) # Int  |-> N)
  **  ((&(( &( "sum" ) )->ₛ "den")) # Int  |-> D)
  **  ((&(( &( "product" ) )->ₛ "num")) # Int  |-> P)
  **  ((&(( &( "product" ) )->ₛ "den")) # Int  |-> Q)
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (((i * 24 ) + j )) (AN_recompute) (0)))
  **  ((&((((&((S_recompute)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (((i * 24 ) + j )) (AD_recompute) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (j) (CN) (0)))
  **  ((&(((&((S_recompute)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (j) (CD) (0)))
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "is_basic") V_recompute IB_recompute )
  **  ((&((S_recompute)  # "SxState" ->ₛ "rows")) # Int  |-> R_recompute)
  **  ((&((S_recompute)  # "SxState" ->ₛ "vars")) # Int  |-> V_recompute)
  **  (IntArray.full &((S_recompute)  # "SxState" ->ₛ "basic") R_recompute B_recompute )
  **  (simplex_recompute_rhs S_recompute R_recompute RN_recompute RD_recompute )
  **  (simplex_recompute_matrix_except S_recompute R_recompute V_recompute AN_recompute AD_recompute i j )
  **  (simplex_recompute_values_except S_recompute V_recompute CN CD j )
.

Definition sx_recompute_partial_solve_wit_5_recompute := sx_recompute_partial_solve_wit_5_recompute_pure -> sx_recompute_partial_solve_wit_5_recompute_aux.

Module Type VC_Correct.


Axiom proof_of_sx_recompute_safety_wit_1_recompute : sx_recompute_safety_wit_1_recompute.
Axiom proof_of_sx_recompute_safety_wit_2_zero_rows : sx_recompute_safety_wit_2_zero_rows.
Axiom proof_of_sx_recompute_safety_wit_3_zero_rows : sx_recompute_safety_wit_3_zero_rows.
Axiom proof_of_sx_recompute_safety_wit_4_recompute : sx_recompute_safety_wit_4_recompute.
Axiom proof_of_sx_recompute_safety_wit_5_recompute : sx_recompute_safety_wit_5_recompute.
Axiom proof_of_sx_recompute_safety_wit_6_recompute : sx_recompute_safety_wit_6_recompute.
Axiom proof_of_sx_recompute_safety_wit_7_recompute : sx_recompute_safety_wit_7_recompute.
Axiom proof_of_sx_recompute_safety_wit_8_recompute : sx_recompute_safety_wit_8_recompute.
Axiom proof_of_sx_recompute_safety_wit_9_recompute : sx_recompute_safety_wit_9_recompute.
Axiom proof_of_sx_recompute_safety_wit_10_recompute : sx_recompute_safety_wit_10_recompute.
Axiom proof_of_sx_recompute_safety_wit_11_recompute : sx_recompute_safety_wit_11_recompute.
Axiom proof_of_sx_recompute_safety_wit_12_recompute : sx_recompute_safety_wit_12_recompute.
Axiom proof_of_sx_recompute_safety_wit_13_recompute : sx_recompute_safety_wit_13_recompute.
Axiom proof_of_sx_recompute_safety_wit_14_recompute : sx_recompute_safety_wit_14_recompute.
Axiom proof_of_sx_recompute_safety_wit_15_recompute : sx_recompute_safety_wit_15_recompute.
Axiom proof_of_sx_recompute_safety_wit_16_recompute : sx_recompute_safety_wit_16_recompute.
Axiom proof_of_sx_recompute_safety_wit_17_recompute : sx_recompute_safety_wit_17_recompute.
Axiom proof_of_sx_recompute_safety_wit_18_recompute : sx_recompute_safety_wit_18_recompute.
Axiom proof_of_sx_recompute_safety_wit_19_recompute : sx_recompute_safety_wit_19_recompute.
Axiom proof_of_sx_recompute_safety_wit_20_recompute : sx_recompute_safety_wit_20_recompute.
Axiom proof_of_sx_recompute_safety_wit_21_recompute : sx_recompute_safety_wit_21_recompute.
Axiom proof_of_sx_recompute_safety_wit_22_recompute : sx_recompute_safety_wit_22_recompute.
Axiom proof_of_sx_recompute_safety_wit_23_recompute : sx_recompute_safety_wit_23_recompute.
Axiom proof_of_sx_recompute_safety_wit_24_recompute : sx_recompute_safety_wit_24_recompute.
Axiom proof_of_sx_recompute_safety_wit_25_zero_rows : sx_recompute_safety_wit_25_zero_rows.
Axiom proof_of_sx_recompute_safety_wit_26_recompute : sx_recompute_safety_wit_26_recompute.
Axiom proof_of_sx_recompute_entail_wit_1_recompute : sx_recompute_entail_wit_1_recompute.
Axiom proof_of_sx_recompute_entail_wit_2_zero_rows : sx_recompute_entail_wit_2_zero_rows.
Axiom proof_of_sx_recompute_entail_wit_3_recompute : sx_recompute_entail_wit_3_recompute.
Axiom proof_of_sx_recompute_entail_wit_4_recompute : sx_recompute_entail_wit_4_recompute.
Axiom proof_of_sx_recompute_entail_wit_5_recompute : sx_recompute_entail_wit_5_recompute.
Axiom proof_of_sx_recompute_entail_wit_6_1_recompute : sx_recompute_entail_wit_6_1_recompute.
Axiom proof_of_sx_recompute_entail_wit_6_2_recompute : sx_recompute_entail_wit_6_2_recompute.
Axiom proof_of_sx_recompute_entail_wit_6_3_recompute : sx_recompute_entail_wit_6_3_recompute.
Axiom proof_of_sx_recompute_entail_wit_6_4_recompute : sx_recompute_entail_wit_6_4_recompute.
Axiom proof_of_sx_recompute_entail_wit_6_5_recompute : sx_recompute_entail_wit_6_5_recompute.
Axiom proof_of_sx_recompute_entail_wit_6_6_recompute : sx_recompute_entail_wit_6_6_recompute.
Axiom proof_of_sx_recompute_entail_wit_7_recompute : sx_recompute_entail_wit_7_recompute.
Axiom proof_of_sx_recompute_entail_wit_8_recompute : sx_recompute_entail_wit_8_recompute.
Axiom proof_of_sx_recompute_return_wit_1_zero_rows : sx_recompute_return_wit_1_zero_rows.
Axiom proof_of_sx_recompute_return_wit_2_recompute : sx_recompute_return_wit_2_recompute.
Axiom proof_of_sx_recompute_return_wit_3_recompute : sx_recompute_return_wit_3_recompute.
Axiom proof_of_sx_recompute_return_wit_4_recompute : sx_recompute_return_wit_4_recompute.
Axiom proof_of_sx_recompute_return_wit_5_recompute : sx_recompute_return_wit_5_recompute.
Axiom proof_of_sx_recompute_partial_solve_wit_1_recompute : sx_recompute_partial_solve_wit_1_recompute.
Axiom proof_of_sx_recompute_partial_solve_wit_2_recompute : sx_recompute_partial_solve_wit_2_recompute.
Axiom proof_of_sx_recompute_partial_solve_wit_3_recompute_pure : sx_recompute_partial_solve_wit_3_recompute_pure.
Axiom proof_of_sx_recompute_partial_solve_wit_3_recompute : sx_recompute_partial_solve_wit_3_recompute.
Axiom proof_of_sx_recompute_partial_solve_wit_4_recompute_pure : sx_recompute_partial_solve_wit_4_recompute_pure.
Axiom proof_of_sx_recompute_partial_solve_wit_4_recompute : sx_recompute_partial_solve_wit_4_recompute.
Axiom proof_of_sx_recompute_partial_solve_wit_5_recompute_pure : sx_recompute_partial_solve_wit_5_recompute_pure.
Axiom proof_of_sx_recompute_partial_solve_wit_5_recompute : sx_recompute_partial_solve_wit_5_recompute.

End VC_Correct.
