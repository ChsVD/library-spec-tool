From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_find_violation_preserve.simplex_find_violation_preserve_lib.
Require Import SimpleC.EE.Applications_human.simplex_find_entering_preserve.simplex_find_entering_preserve_lib.
Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib.
Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib.
Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib.
Local Open Scope sac.

(*----- Function sx_solve -----*)

Definition sx_solve_safety_wit_1_negative_budget :=
forall (L_negative_budget: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre = L_negative_budget)) (PreH2 : ((INT_MIN) <= L_negative_budget)) (PreH3 : (L_negative_budget < 0)),
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_2_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= L_normal_state)) (PreH4 : (L_normal_state <= INT_MAX)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : ((Zlength (N_normal_state)) = 400)) (PreH13 : ((Zlength (D_normal_state)) = 400)) (PreH14 : ((Zlength (B_normal_state)) = M_normal_state)) (PreH15 : ((Zlength (IB_normal_state)) = V_normal_state)) (PreH16 : ((Zlength (HL_normal_state)) = V_normal_state)) (PreH17 : ((Zlength (HU_normal_state)) = V_normal_state)) (PreH18 : ((Zlength (LN_normal_state)) = V_normal_state)) (PreH19 : ((Zlength (LD_normal_state)) = V_normal_state)) (PreH20 : ((Zlength (UN_normal_state)) = V_normal_state)) (PreH21 : ((Zlength (UD_normal_state)) = V_normal_state)) (PreH22 : ((Zlength (VN_normal_state)) = V_normal_state)) (PreH23 : ((Zlength (VD_normal_state)) = V_normal_state)) (PreH24 : forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= j)) /\ (j <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_normal_state) (0))) /\ ((Znth (((i * 9 ) + j )) (A_normal_state) (0)) <= INT_MAX)))) (PreH25 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )) (PreH26 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )),
  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state B_normal_state )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state IB_normal_state )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state N_normal_state D_normal_state )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state VN_normal_state VD_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_3_negative_budget :=
forall (L_negative_budget: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre = L_negative_budget)) (PreH2 : ((INT_MIN) <= L_negative_budget)) (PreH3 : (L_negative_budget < 0)),
  ((( &( "leaving" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_4_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= L_normal_state)) (PreH4 : (L_normal_state <= INT_MAX)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : ((Zlength (N_normal_state)) = 400)) (PreH13 : ((Zlength (D_normal_state)) = 400)) (PreH14 : ((Zlength (B_normal_state)) = M_normal_state)) (PreH15 : ((Zlength (IB_normal_state)) = V_normal_state)) (PreH16 : ((Zlength (HL_normal_state)) = V_normal_state)) (PreH17 : ((Zlength (HU_normal_state)) = V_normal_state)) (PreH18 : ((Zlength (LN_normal_state)) = V_normal_state)) (PreH19 : ((Zlength (LD_normal_state)) = V_normal_state)) (PreH20 : ((Zlength (UN_normal_state)) = V_normal_state)) (PreH21 : ((Zlength (UD_normal_state)) = V_normal_state)) (PreH22 : ((Zlength (VN_normal_state)) = V_normal_state)) (PreH23 : ((Zlength (VD_normal_state)) = V_normal_state)) (PreH24 : forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= j)) /\ (j <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_normal_state) (0))) /\ ((Znth (((i * 9 ) + j )) (A_normal_state) (0)) <= INT_MAX)))) (PreH25 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )) (PreH26 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )),
  ((( &( "leaving" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state B_normal_state )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state IB_normal_state )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state N_normal_state D_normal_state )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state VN_normal_state VD_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_5_negative_budget :=
forall (L_negative_budget: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre >= 0)) (PreH2 : (pivot_limit_pre = L_negative_budget)) (PreH3 : ((INT_MIN) <= L_negative_budget)) (PreH4 : (L_negative_budget < 0)),
  ((( &( "leaving" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ False ”
.

Definition sx_solve_safety_wit_6_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= L_normal_state)) (PreH5 : (L_normal_state <= INT_MAX)) (PreH6 : (0 <= M_normal_state)) (PreH7 : (M_normal_state <= 16)) (PreH8 : (0 <= I_normal_state)) (PreH9 : (I_normal_state <= 8)) (PreH10 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH11 : (0 <= V_normal_state)) (PreH12 : (V_normal_state <= 24)) (PreH13 : ((Zlength (N_normal_state)) = 400)) (PreH14 : ((Zlength (D_normal_state)) = 400)) (PreH15 : ((Zlength (B_normal_state)) = M_normal_state)) (PreH16 : ((Zlength (IB_normal_state)) = V_normal_state)) (PreH17 : ((Zlength (HL_normal_state)) = V_normal_state)) (PreH18 : ((Zlength (HU_normal_state)) = V_normal_state)) (PreH19 : ((Zlength (LN_normal_state)) = V_normal_state)) (PreH20 : ((Zlength (LD_normal_state)) = V_normal_state)) (PreH21 : ((Zlength (UN_normal_state)) = V_normal_state)) (PreH22 : ((Zlength (UD_normal_state)) = V_normal_state)) (PreH23 : ((Zlength (VN_normal_state)) = V_normal_state)) (PreH24 : ((Zlength (VD_normal_state)) = V_normal_state)) (PreH25 : forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= j)) /\ (j <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_normal_state) (0))) /\ ((Znth (((i * 9 ) + j )) (A_normal_state) (0)) <= INT_MAX)))) (PreH26 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )) (PreH27 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )),
  ((( &( "leaving" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state B_normal_state )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state IB_normal_state )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state N_normal_state D_normal_state )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state VN_normal_state VD_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ False ”
.

Definition sx_solve_safety_wit_7_negative_budget :=
forall (L_negative_budget: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre < 0)) (PreH2 : (pivot_limit_pre = L_negative_budget)) (PreH3 : ((INT_MIN) <= L_negative_budget)) (PreH4 : (L_negative_budget < 0)),
  ((( &( "leaving" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_8_negative_budget :=
forall (L_negative_budget: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre < 0)) (PreH2 : (pivot_limit_pre = L_negative_budget)) (PreH3 : ((INT_MIN) <= L_negative_budget)) (PreH4 : (L_negative_budget < 0)),
  ((( &( "leaving" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_9_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_10_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (R: Z) (D: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state retval R D )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |-> R)
  **  ((( &( "direction" ) )) # Int  |-> D)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_11_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (R: Z) (D: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state retval R D )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |-> R)
  **  ((( &( "direction" ) )) # Int  |-> D)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_12_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_13_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (row < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_14_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((( &( "entering" ) )) # Int  |-> e)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_15_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((( &( "entering" ) )) # Int  |-> e)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_16_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((( &( "entering" ) )) # Int  |-> e)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_17_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((( &( "entering" ) )) # Int  |-> e)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_18_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH18 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH19 : (0 <= row)) (PreH20 : (row < M_normal_state)) (PreH21 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_19_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH18 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH19 : (0 <= row)) (PreH20 : (row < M_normal_state)) (PreH21 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_20_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (entering < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH19 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_21_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (entering < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH19 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_22_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count >= pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_23_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count >= pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_24_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count >= pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_25_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count >= pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_26_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ False ”
.

Definition sx_solve_safety_wit_27_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ False ”
.

Definition sx_solve_safety_wit_28_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ False ”
.

Definition sx_solve_safety_wit_29_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 1)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ False ”
.

Definition sx_solve_safety_wit_30_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_31_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_32_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_33_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON) (0))) /\ ((Znth (k) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD) (1)))) /\ ((Znth (k) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON) (0))))) ((Znth (k) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_34_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (0 <= row)) (PreH18 : (row < M_normal_state)) (PreH19 : (0 <= entering)) (PreH20 : (entering < V_normal_state)) (PreH21 : (0 <= leaving)) (PreH22 : (leaving < V_normal_state)) (PreH23 : (leaving = (Znth (row) (CB) (0)))) (PreH24 : (count < L_normal_state)) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH27 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH28 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH29 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH30 : ((Zlength (PN)) = 400)) (PreH31 : ((Zlength (PD)) = 400)) (PreH32 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (CVN) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (CVD) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_solve_safety_wit_35_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH3 : (Forall (Z.ge (INT_MAX)) ON )) (PreH4 : (Forall (Z.le (1)) OD )) (PreH5 : (Forall (Z.ge (INT_MAX)) OD )) (PreH6 : ((Zlength (ON)) = V_normal_state)) (PreH7 : ((Zlength (OD)) = V_normal_state)) (PreH8 : (simplex_recompute_prefix (simplex_pivot_marks (CIB) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) M_normal_state V_normal_state retval ON OD )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (0 <= row)) (PreH26 : (row < M_normal_state)) (PreH27 : (0 <= entering)) (PreH28 : (entering < V_normal_state)) (PreH29 : (0 <= leaving)) (PreH30 : (leaving < V_normal_state)) (PreH31 : (leaving = (Znth (row) (CB) (0)))) (PreH32 : (count < L_normal_state)) (PreH33 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH34 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH35 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH36 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH37 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH38 : ((Zlength (PN)) = 400)) (PreH39 : ((Zlength (PD)) = 400)) (PreH40 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_solve_safety_wit_36_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH3 : (Forall (Z.ge (INT_MAX)) ON )) (PreH4 : (Forall (Z.le (1)) OD )) (PreH5 : (Forall (Z.ge (INT_MAX)) OD )) (PreH6 : ((Zlength (ON)) = V_normal_state)) (PreH7 : ((Zlength (OD)) = V_normal_state)) (PreH8 : (simplex_recompute_prefix (simplex_pivot_marks (CIB) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) M_normal_state V_normal_state retval ON OD )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (0 <= row)) (PreH26 : (row < M_normal_state)) (PreH27 : (0 <= entering)) (PreH28 : (entering < V_normal_state)) (PreH29 : (0 <= leaving)) (PreH30 : (leaving < V_normal_state)) (PreH31 : (leaving = (Znth (row) (CB) (0)))) (PreH32 : (count < L_normal_state)) (PreH33 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH34 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH35 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH36 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH37 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH38 : ((Zlength (PN)) = 400)) (PreH39 : ((Zlength (PD)) = 400)) (PreH40 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_solve_safety_wit_37_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH3 : (Forall (Z.ge (INT_MAX)) ON )) (PreH4 : (Forall (Z.le (1)) OD )) (PreH5 : (Forall (Z.ge (INT_MAX)) OD )) (PreH6 : ((Zlength (ON)) = V_normal_state)) (PreH7 : ((Zlength (OD)) = V_normal_state)) (PreH8 : (simplex_recompute_prefix (simplex_pivot_marks (CIB) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) M_normal_state V_normal_state retval ON OD )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (0 <= row)) (PreH26 : (row < M_normal_state)) (PreH27 : (0 <= entering)) (PreH28 : (entering < V_normal_state)) (PreH29 : (0 <= leaving)) (PreH30 : (leaving < V_normal_state)) (PreH31 : (leaving = (Znth (row) (CB) (0)))) (PreH32 : (count < L_normal_state)) (PreH33 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH34 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH35 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH36 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH37 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH38 : ((Zlength (PN)) = 400)) (PreH39 : ((Zlength (PD)) = 400)) (PreH40 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON OD )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((count + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition sx_solve_entail_wit_1_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre >= 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= L_normal_state)) (PreH5 : (L_normal_state <= INT_MAX)) (PreH6 : (0 <= M_normal_state)) (PreH7 : (M_normal_state <= 16)) (PreH8 : (0 <= I_normal_state)) (PreH9 : (I_normal_state <= 8)) (PreH10 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH11 : (0 <= V_normal_state)) (PreH12 : (V_normal_state <= 24)) (PreH13 : ((Zlength (N_normal_state)) = 400)) (PreH14 : ((Zlength (D_normal_state)) = 400)) (PreH15 : ((Zlength (B_normal_state)) = M_normal_state)) (PreH16 : ((Zlength (IB_normal_state)) = V_normal_state)) (PreH17 : ((Zlength (HL_normal_state)) = V_normal_state)) (PreH18 : ((Zlength (HU_normal_state)) = V_normal_state)) (PreH19 : ((Zlength (LN_normal_state)) = V_normal_state)) (PreH20 : ((Zlength (LD_normal_state)) = V_normal_state)) (PreH21 : ((Zlength (UN_normal_state)) = V_normal_state)) (PreH22 : ((Zlength (UD_normal_state)) = V_normal_state)) (PreH23 : ((Zlength (VN_normal_state)) = V_normal_state)) (PreH24 : ((Zlength (VD_normal_state)) = V_normal_state)) (PreH25 : forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= j)) /\ (j <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_normal_state) (0))) /\ ((Znth (((i * 9 ) + j )) (A_normal_state) (0)) <= INT_MAX)))) (PreH26 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )) (PreH27 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state B_normal_state )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state IB_normal_state )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state N_normal_state D_normal_state )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state VN_normal_state VD_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state 0 N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre >= 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= L_normal_state)) (PreH5 : (L_normal_state <= INT_MAX)) (PreH6 : (0 <= M_normal_state)) (PreH7 : (M_normal_state <= 16)) (PreH8 : (0 <= I_normal_state)) (PreH9 : (I_normal_state <= 8)) (PreH10 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH11 : (0 <= V_normal_state)) (PreH12 : (V_normal_state <= 24)) (PreH13 : ((Zlength (N_normal_state)) = 400)) (PreH14 : ((Zlength (D_normal_state)) = 400)) (PreH15 : ((Zlength (B_normal_state)) = M_normal_state)) (PreH16 : ((Zlength (IB_normal_state)) = V_normal_state)) (PreH17 : ((Zlength (HL_normal_state)) = V_normal_state)) (PreH18 : ((Zlength (HU_normal_state)) = V_normal_state)) (PreH19 : ((Zlength (LN_normal_state)) = V_normal_state)) (PreH20 : ((Zlength (LD_normal_state)) = V_normal_state)) (PreH21 : ((Zlength (UN_normal_state)) = V_normal_state)) (PreH22 : ((Zlength (UD_normal_state)) = V_normal_state)) (PreH23 : ((Zlength (VN_normal_state)) = V_normal_state)) (PreH24 : ((Zlength (VD_normal_state)) = V_normal_state)) (PreH25 : forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= j)) /\ (j <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_normal_state) (0))) /\ ((Znth (((i * 9 ) + j )) (A_normal_state) (0)) <= INT_MAX)))) (PreH26 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )) (PreH27 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )),
  TT && emp 
|--
  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state (M_normal_state + I_normal_state ) L_normal_state 0 N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state ) ”
  &&  emp
).

Definition sx_solve_entail_wit_1_normal_state_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre >= 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= L_normal_state)) (PreH5 : (L_normal_state <= INT_MAX)) (PreH6 : (0 <= M_normal_state)) (PreH7 : (M_normal_state <= 16)) (PreH8 : (0 <= I_normal_state)) (PreH9 : (I_normal_state <= 8)) (PreH10 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH11 : (0 <= V_normal_state)) (PreH12 : (V_normal_state <= 24)) (PreH13 : ((Zlength (N_normal_state)) = 400)) (PreH14 : ((Zlength (D_normal_state)) = 400)) (PreH15 : ((Zlength (B_normal_state)) = M_normal_state)) (PreH16 : ((Zlength (IB_normal_state)) = V_normal_state)) (PreH17 : ((Zlength (HL_normal_state)) = V_normal_state)) (PreH18 : ((Zlength (HU_normal_state)) = V_normal_state)) (PreH19 : ((Zlength (LN_normal_state)) = V_normal_state)) (PreH20 : ((Zlength (LD_normal_state)) = V_normal_state)) (PreH21 : ((Zlength (UN_normal_state)) = V_normal_state)) (PreH22 : ((Zlength (UD_normal_state)) = V_normal_state)) (PreH23 : ((Zlength (VN_normal_state)) = V_normal_state)) (PreH24 : ((Zlength (VD_normal_state)) = V_normal_state)) (PreH25 : forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= j)) /\ (j <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_normal_state) (0))) /\ ((Znth (((i * 9 ) + j )) (A_normal_state) (0)) <= INT_MAX)))) (PreH26 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )) (PreH27 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) )),
  (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state (M_normal_state + I_normal_state ) L_normal_state 0 N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state )
.

Definition sx_solve_entail_wit_2_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB_2 )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB_2 )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN_2 CD_2 )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )),
  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN_2 CD_2 )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB_2 CVN CVD ) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_entail_wit_3_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (R: Z) (D: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state retval R D )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB_2 )
  **  (simplex_scan_read_memory s_pre CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB_2 )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN_2 CD_2 )
  **  (simplex_solve_read_rest s_pre V_normal_state CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 R D ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (R: Z) (D: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state retval R D )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )),
  (simplex_scan_read_memory s_pre CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN_2 CD_2 )
  **  (simplex_solve_read_rest s_pre V_normal_state CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB_2 CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 R D ) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_entail_wit_4_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (row >= 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH18 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB_2 )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB_2 )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN_2 CD_2 )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  (EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = 1) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row ))
  ||
  (EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = (-1)) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row ))
.

Definition sx_solve_entail_wit_5_1_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH19 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB_2 )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB_2 )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN_2 CD_2 row )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 e ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = 1) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH19 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN_2 CD_2 row )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB_2 CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 e ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = 1) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_entail_wit_5_2_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH19 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB_2 )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB_2 )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN_2 CD_2 row )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 e ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = (-1)) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH19 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN_2) (row) ((M_normal_state + I_normal_state ))) )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN_2 CD_2 row )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB_2) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB_2 CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 e ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = (-1)) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_entail_wit_6_1_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN_2 CD_2 ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN_2 CD_2 ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (ON) (0))) /\ ((Znth (k_2) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (OD) (1)))) /\ ((Znth (k_2) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (ON) (0))))) ((Znth (k_2) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB CIB_2 CVN_2 CVD_2 )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB_2) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB_2: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= (Znth row CB 0)) ”
  &&  “ ((Znth row CB 0) < V_normal_state) ”
  &&  “ ((Znth row CB 0) = (Znth (row) (CB_2) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth row CB 0) 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering (Znth row CB 0) ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB_2 M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB_2) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth row CB 0)) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD (Znth row CB 0) )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state (Znth row CB 0) )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (CVN) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (CVD) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HU_normal_state) (0)))
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN_2 CD_2 ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN_2 CD_2 ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (ON) (0))) /\ ((Znth (k_2) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (OD) (1)))) /\ ((Znth (k_2) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (ON) (0))))) ((Znth (k_2) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB CIB_2 CVN_2 CVD_2 )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB_2: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ ((simplex_pivot_marks (CIB_2) ((Znth (row) (CB) (0))) (entering) (retval)) = (simplex_pivot_marks (CIB) ((Znth row CB 0)) (entering) (1))) ”
  &&  “ ((simplex_pivot_basis (CB) (row) (entering) (retval)) = (simplex_pivot_basis (CB_2) (row) (entering) (1))) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= (Znth row CB 0)) ”
  &&  “ ((Znth row CB 0) < V_normal_state) ”
  &&  “ ((Znth row CB 0) = (Znth (row) (CB_2) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth row CB 0) 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering (Znth row CB 0) ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB_2 M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD (Znth row CB 0) )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state (Znth row CB 0) )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (CVN) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (CVD) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HU_normal_state) (0)))
).

Definition sx_solve_entail_wit_6_2_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN_2 CD_2 ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN_2 CD_2 ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (ON) (0))) /\ ((Znth (k_2) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (OD) (1)))) /\ ((Znth (k_2) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (ON) (0))))) ((Znth (k_2) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB CIB_2 CVN_2 CVD_2 )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB_2) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB_2: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= (Znth row CB 0)) ”
  &&  “ ((Znth row CB 0) < V_normal_state) ”
  &&  “ ((Znth row CB 0) = (Znth (row) (CB_2) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth row CB 0) 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering (Znth row CB 0) ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB_2 M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB_2) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth row CB 0)) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD (Znth row CB 0) )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state (Znth row CB 0) )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (CVN) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (CVD) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HU_normal_state) (0)))
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON: (@list Z)) (OD: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = 1)) (PreH3 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON OD )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN_2 CD_2 ON OD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN_2 CD_2 ON OD CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (ON) (0))) /\ ((Znth (k_2) (ON) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (OD) (1)))) /\ ((Znth (k_2) (OD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (ON) (0))))) ((Znth (k_2) (OD) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB) (CIB_2) (CVN_2) (CVD_2)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB CIB_2 CVN_2 CVD_2 )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB_2: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ ((simplex_pivot_marks (CIB_2) ((Znth (row) (CB) (0))) (entering) (retval)) = (simplex_pivot_marks (CIB) ((Znth row CB 0)) (entering) (1))) ”
  &&  “ ((simplex_pivot_basis (CB) (row) (entering) (retval)) = (simplex_pivot_basis (CB_2) (row) (entering) (1))) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB_2) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB_2 CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= (Znth row CB 0)) ”
  &&  “ ((Znth row CB 0) < V_normal_state) ”
  &&  “ ((Znth row CB 0) = (Znth (row) (CB_2) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth row CB 0) 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering (Znth row CB 0) ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB_2 M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD (Znth row CB 0) )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state (Znth row CB 0) )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (CVN) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (CVD) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((Znth row CB 0)) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + ((Znth row CB 0) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth ((Znth row CB 0)) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + ((Znth row CB 0) * sizeof(INT)))) # Int  |-> (Znth ((Znth row CB 0)) (HU_normal_state) (0)))
).

Definition sx_solve_entail_wit_7_1_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (PN_2: (@list Z)) (PD_2: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (direction > 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (0 <= entering)) (PreH21 : (entering < V_normal_state)) (PreH22 : (0 <= leaving)) (PreH23 : (leaving < V_normal_state)) (PreH24 : (leaving = (Znth (row) (CB_2) (0)))) (PreH25 : (count < L_normal_state)) (PreH26 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH27 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH28 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering leaving 1 PN_2 PD_2 )) (PreH29 : (simplex_pivot_closed CN_2 CD_2 PN_2 PD_2 M_normal_state V_normal_state row entering leaving )) (PreH30 : (simplex_pivot_equiv CN_2 CD_2 PN_2 PD_2 CB_2 M_normal_state V_normal_state row entering )) (PreH31 : ((Zlength (PN_2)) = 400)) (PreH32 : ((Zlength (PD_2)) = 400)) (PreH33 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN_2) (0))) /\ ((Znth (k_2) (PN_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD_2) (1)))) /\ ((Znth (k_2) (PD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN_2) (0))))) ((Znth (k_2) (PD_2) (1)))) = 1)))),
  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB_2) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN_2 PD_2 )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN_2 CVD_2 leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (PN_2: (@list Z)) (PD_2: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : ((Znth (leaving) (HU_normal_state) (0)) <= INT_MAX)) (PreH2 : ((Znth (leaving) (HL_normal_state) (0)) <= INT_MAX)) (PreH3 : ((Znth (leaving) (UD_normal_state) (0)) <= INT_MAX)) (PreH4 : ((Znth (leaving) (UN_normal_state) (0)) <= INT_MAX)) (PreH5 : ((Znth (leaving) (LN_normal_state) (0)) <= INT_MAX)) (PreH6 : ((Znth (leaving) (LD_normal_state) (0)) <= INT_MAX)) (PreH7 : ((Znth (leaving) (HU_normal_state) (0)) >= INT_MIN)) (PreH8 : ((Znth (leaving) (HL_normal_state) (0)) >= INT_MIN)) (PreH9 : ((Znth (leaving) (UD_normal_state) (0)) >= INT_MIN)) (PreH10 : ((Znth (leaving) (UN_normal_state) (0)) >= INT_MIN)) (PreH11 : ((Znth (leaving) (LN_normal_state) (0)) >= INT_MIN)) (PreH12 : ((Znth (leaving) (LD_normal_state) (0)) >= INT_MIN)) (PreH13 : (direction > 0)) (PreH14 : (s_pre = S_normal_state)) (PreH15 : (pivot_limit_pre = L_normal_state)) (PreH16 : (0 <= M_normal_state)) (PreH17 : (M_normal_state <= 16)) (PreH18 : (0 <= I_normal_state)) (PreH19 : (I_normal_state <= 8)) (PreH20 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH21 : (0 <= V_normal_state)) (PreH22 : (V_normal_state <= 24)) (PreH23 : (0 <= L_normal_state)) (PreH24 : (L_normal_state <= INT_MAX)) (PreH25 : (0 <= count)) (PreH26 : (count <= L_normal_state)) (PreH27 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH28 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH29 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH30 : (0 <= row)) (PreH31 : (row < M_normal_state)) (PreH32 : (0 <= entering)) (PreH33 : (entering < V_normal_state)) (PreH34 : (0 <= leaving)) (PreH35 : (leaving < V_normal_state)) (PreH36 : (leaving = (Znth (row) (CB_2) (0)))) (PreH37 : (count < L_normal_state)) (PreH38 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH39 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH40 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering leaving 1 PN_2 PD_2 )) (PreH41 : (simplex_pivot_closed CN_2 CD_2 PN_2 PD_2 M_normal_state V_normal_state row entering leaving )) (PreH42 : (simplex_pivot_equiv CN_2 CD_2 PN_2 PD_2 CB_2 M_normal_state V_normal_state row entering )) (PreH43 : ((Zlength (PN_2)) = 400)) (PreH44 : ((Zlength (PD_2)) = 400)) (PreH45 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN_2) (0))) /\ ((Znth (k_2) (PN_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD_2) (1)))) /\ ((Znth (k_2) (PD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN_2) (0))))) ((Znth (k_2) (PD_2) (1)))) = 1)))),
  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN_2 PD_2 )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN_2 CVD_2 leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ ((simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) = (simplex_pivot_marks (CIB) (leaving) (entering) (1))) ”
  &&  “ ((simplex_pivot_basis (CB_2) (row) (entering) (1)) = (simplex_pivot_basis (CB) (row) (entering) (1))) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_entail_wit_7_2_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (PN_2: (@list Z)) (PD_2: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (direction <= 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (0 <= entering)) (PreH21 : (entering < V_normal_state)) (PreH22 : (0 <= leaving)) (PreH23 : (leaving < V_normal_state)) (PreH24 : (leaving = (Znth (row) (CB_2) (0)))) (PreH25 : (count < L_normal_state)) (PreH26 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH27 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH28 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering leaving 1 PN_2 PD_2 )) (PreH29 : (simplex_pivot_closed CN_2 CD_2 PN_2 PD_2 M_normal_state V_normal_state row entering leaving )) (PreH30 : (simplex_pivot_equiv CN_2 CD_2 PN_2 PD_2 CB_2 M_normal_state V_normal_state row entering )) (PreH31 : ((Zlength (PN_2)) = 400)) (PreH32 : ((Zlength (PD_2)) = 400)) (PreH33 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN_2) (0))) /\ ((Znth (k_2) (PN_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD_2) (1)))) /\ ((Znth (k_2) (PD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN_2) (0))))) ((Znth (k_2) (PD_2) (1)))) = 1)))),
  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB_2) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN_2 PD_2 )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN_2 CVD_2 leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (PN_2: (@list Z)) (PD_2: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : ((Znth (leaving) (HU_normal_state) (0)) <= INT_MAX)) (PreH2 : ((Znth (leaving) (HL_normal_state) (0)) <= INT_MAX)) (PreH3 : ((Znth (leaving) (LD_normal_state) (0)) <= INT_MAX)) (PreH4 : ((Znth (leaving) (LN_normal_state) (0)) <= INT_MAX)) (PreH5 : ((Znth (leaving) (UN_normal_state) (0)) <= INT_MAX)) (PreH6 : ((Znth (leaving) (UD_normal_state) (0)) <= INT_MAX)) (PreH7 : ((Znth (leaving) (HU_normal_state) (0)) >= INT_MIN)) (PreH8 : ((Znth (leaving) (HL_normal_state) (0)) >= INT_MIN)) (PreH9 : ((Znth (leaving) (LD_normal_state) (0)) >= INT_MIN)) (PreH10 : ((Znth (leaving) (LN_normal_state) (0)) >= INT_MIN)) (PreH11 : ((Znth (leaving) (UN_normal_state) (0)) >= INT_MIN)) (PreH12 : ((Znth (leaving) (UD_normal_state) (0)) >= INT_MIN)) (PreH13 : (direction <= 0)) (PreH14 : (s_pre = S_normal_state)) (PreH15 : (pivot_limit_pre = L_normal_state)) (PreH16 : (0 <= M_normal_state)) (PreH17 : (M_normal_state <= 16)) (PreH18 : (0 <= I_normal_state)) (PreH19 : (I_normal_state <= 8)) (PreH20 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH21 : (0 <= V_normal_state)) (PreH22 : (V_normal_state <= 24)) (PreH23 : (0 <= L_normal_state)) (PreH24 : (L_normal_state <= INT_MAX)) (PreH25 : (0 <= count)) (PreH26 : (count <= L_normal_state)) (PreH27 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH28 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH29 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH30 : (0 <= row)) (PreH31 : (row < M_normal_state)) (PreH32 : (0 <= entering)) (PreH33 : (entering < V_normal_state)) (PreH34 : (0 <= leaving)) (PreH35 : (leaving < V_normal_state)) (PreH36 : (leaving = (Znth (row) (CB_2) (0)))) (PreH37 : (count < L_normal_state)) (PreH38 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH39 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH40 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering leaving 1 PN_2 PD_2 )) (PreH41 : (simplex_pivot_closed CN_2 CD_2 PN_2 PD_2 M_normal_state V_normal_state row entering leaving )) (PreH42 : (simplex_pivot_equiv CN_2 CD_2 PN_2 PD_2 CB_2 M_normal_state V_normal_state row entering )) (PreH43 : ((Zlength (PN_2)) = 400)) (PreH44 : ((Zlength (PD_2)) = 400)) (PreH45 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN_2) (0))) /\ ((Znth (k_2) (PN_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD_2) (1)))) /\ ((Znth (k_2) (PD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN_2) (0))))) ((Znth (k_2) (PD_2) (1)))) = 1)))),
  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN_2 PD_2 )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN_2 CVD_2 leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  EX (PN: (@list Z)) (PD: (@list Z)) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ ((simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) = (simplex_pivot_marks (CIB) (leaving) (entering) (1))) ”
  &&  “ ((simplex_pivot_basis (CB_2) (row) (entering) (1)) = (simplex_pivot_basis (CB) (row) (entering) (1))) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_entail_wit_8_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH3 : (Forall (Z.ge (INT_MAX)) ON )) (PreH4 : (Forall (Z.le (1)) OD )) (PreH5 : (Forall (Z.ge (INT_MAX)) OD )) (PreH6 : ((Zlength (ON)) = V_normal_state)) (PreH7 : ((Zlength (OD)) = V_normal_state)) (PreH8 : (simplex_recompute_prefix (simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB_2) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN_2) ((Znth (row) (CB_2) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD_2) ((Znth (row) (CB_2) (0))) (direction)) M_normal_state V_normal_state retval ON OD )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH25 : (0 <= row)) (PreH26 : (row < M_normal_state)) (PreH27 : (0 <= entering)) (PreH28 : (entering < V_normal_state)) (PreH29 : (0 <= leaving)) (PreH30 : (leaving < V_normal_state)) (PreH31 : (leaving = (Znth (row) (CB_2) (0)))) (PreH32 : (count < L_normal_state)) (PreH33 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH34 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH35 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH36 : (simplex_pivot_closed CN_2 CD_2 PN PD M_normal_state V_normal_state row entering leaving )) (PreH37 : (simplex_pivot_equiv CN_2 CD_2 PN PD CB_2 M_normal_state V_normal_state row entering )) (PreH38 : ((Zlength (PN)) = 400)) (PreH39 : ((Zlength (PD)) = 400)) (PreH40 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB_2) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON OD )
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state (count + 1 ) N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN_2: (@list Z)) (CD_2: (@list Z)) (CB_2: (@list Z)) (CIB_2: (@list Z)) (CVN_2: (@list Z)) (CVD_2: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH3 : (Forall (Z.ge (INT_MAX)) ON )) (PreH4 : (Forall (Z.le (1)) OD )) (PreH5 : (Forall (Z.ge (INT_MAX)) OD )) (PreH6 : ((Zlength (ON)) = V_normal_state)) (PreH7 : ((Zlength (OD)) = V_normal_state)) (PreH8 : (simplex_recompute_prefix (simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB_2) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN_2) ((Znth (row) (CB_2) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD_2) ((Znth (row) (CB_2) (0))) (direction)) M_normal_state V_normal_state retval ON OD )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN_2) (CD_2) (CB_2) (CIB_2) (CVN_2) (CVD_2)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN_2 CD_2 CB_2 CIB_2 CVN_2 CVD_2 )) (PreH25 : (0 <= row)) (PreH26 : (row < M_normal_state)) (PreH27 : (0 <= entering)) (PreH28 : (entering < V_normal_state)) (PreH29 : (0 <= leaving)) (PreH30 : (leaving < V_normal_state)) (PreH31 : (leaving = (Znth (row) (CB_2) (0)))) (PreH32 : (count < L_normal_state)) (PreH33 : (simplex_find_violation_spec CB_2 HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH34 : (simplex_find_entering_spec CIB_2 (simplex_solve_row (CN_2) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN_2 CVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH35 : (simplex_pivot_result CN_2 CD_2 M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH36 : (simplex_pivot_closed CN_2 CD_2 PN PD M_normal_state V_normal_state row entering leaving )) (PreH37 : (simplex_pivot_equiv CN_2 CD_2 PN PD CB_2 M_normal_state V_normal_state row entering )) (PreH38 : ((Zlength (PN)) = 400)) (PreH39 : ((Zlength (PD)) = 400)) (PreH40 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON OD )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (CN: (@list Z)) (CD: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)),
  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= (count + 1 )) ”
  &&  “ ((count + 1 ) <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) ((simplex_pivot_basis (CB_2) (row) (entering) (1))) ((simplex_pivot_marks (CIB_2) (leaving) (entering) (1))) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) ((simplex_pivot_basis (CB_2) (row) (entering) (1))) ((simplex_pivot_marks (CIB_2) (leaving) (entering) (1))) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state (count + 1 ) N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD (simplex_pivot_basis (CB_2) (row) (entering) (1)) (simplex_pivot_marks (CIB_2) (leaving) (entering) (1)) CVN CVD ) ”
  &&  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_1_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD_2: (@list Z)) (ON_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (Forall (Z.le ((-INT_MAX))) ON_2 )) (PreH3 : (Forall (Z.ge (INT_MAX)) ON_2 )) (PreH4 : (Forall (Z.le (1)) OD_2 )) (PreH5 : (Forall (Z.ge (INT_MAX)) OD_2 )) (PreH6 : ((Zlength (ON_2)) = V_normal_state)) (PreH7 : ((Zlength (OD_2)) = V_normal_state)) (PreH8 : (simplex_recompute_prefix (simplex_pivot_marks (CIB) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) M_normal_state V_normal_state retval ON_2 OD_2 )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (0 <= row)) (PreH26 : (row < M_normal_state)) (PreH27 : (0 <= entering)) (PreH28 : (entering < V_normal_state)) (PreH29 : (0 <= leaving)) (PreH30 : (leaving < V_normal_state)) (PreH31 : (leaving = (Znth (row) (CB) (0)))) (PreH32 : (count < L_normal_state)) (PreH33 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH34 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH35 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH36 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH37 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH38 : ((Zlength (PN)) = 400)) (PreH39 : ((Zlength (PD)) = 400)) (PreH40 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON_2 OD_2 )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (OD_2: (@list Z)) (ON_2: (@list Z)) (retval: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (retval = 0)) (PreH8 : (Forall (Z.le ((-INT_MAX))) ON_2 )) (PreH9 : (Forall (Z.ge (INT_MAX)) ON_2 )) (PreH10 : (Forall (Z.le (1)) OD_2 )) (PreH11 : (Forall (Z.ge (INT_MAX)) OD_2 )) (PreH12 : ((Zlength (ON_2)) = V_normal_state)) (PreH13 : ((Zlength (OD_2)) = V_normal_state)) (PreH14 : (simplex_recompute_prefix (simplex_pivot_marks (CIB) (leaving) (entering) (1)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) (simplex_pivot_basis (CB) (row) (entering) (1)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) M_normal_state V_normal_state retval ON_2 OD_2 )) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (0 <= row)) (PreH32 : (row < M_normal_state)) (PreH33 : (0 <= entering)) (PreH34 : (entering < V_normal_state)) (PreH35 : (0 <= leaving)) (PreH36 : (leaving < V_normal_state)) (PreH37 : (leaving = (Znth (row) (CB) (0)))) (PreH38 : (count < L_normal_state)) (PreH39 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH40 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH41 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH42 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH43 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH44 : ((Zlength (PN)) = 400)) (PreH45 : ((Zlength (PD)) = 400)) (PreH46 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state ON_2 OD_2 )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_2_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON_2 OD_2 )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON_2 OD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON_2 OD_2 CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON_2) (0))) /\ ((Znth (k) (ON_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD_2) (1)))) /\ ((Znth (k) (OD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON_2) (0))))) ((Znth (k) (OD_2) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON_2 OD_2 )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (retval: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (retval = 0)) (PreH8 : (retval = 0)) (PreH9 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON_2 OD_2 )) (PreH10 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON_2 OD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON_2 OD_2 CB M_normal_state V_normal_state row entering )))) (PreH11 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON_2) (0))) /\ ((Znth (k) (ON_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD_2) (1)))) /\ ((Znth (k) (OD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON_2) (0))))) ((Znth (k) (OD_2) (1)))) = 1)))) (PreH12 : (count < pivot_limit_pre)) (PreH13 : (entering >= 0)) (PreH14 : (s_pre = S_normal_state)) (PreH15 : (pivot_limit_pre = L_normal_state)) (PreH16 : (0 <= M_normal_state)) (PreH17 : (M_normal_state <= 16)) (PreH18 : (0 <= I_normal_state)) (PreH19 : (I_normal_state <= 8)) (PreH20 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH21 : (0 <= V_normal_state)) (PreH22 : (V_normal_state <= 24)) (PreH23 : (0 <= L_normal_state)) (PreH24 : (L_normal_state <= INT_MAX)) (PreH25 : (0 <= count)) (PreH26 : (count <= L_normal_state)) (PreH27 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH28 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH30 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH31 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON_2 OD_2 )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_3_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = 0)) (PreH3 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON_2 OD_2 )) (PreH4 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON_2 OD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON_2 OD_2 CB M_normal_state V_normal_state row entering )))) (PreH5 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON_2) (0))) /\ ((Znth (k) (ON_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD_2) (1)))) /\ ((Znth (k) (OD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON_2) (0))))) ((Znth (k) (OD_2) (1)))) = 1)))) (PreH6 : (count < pivot_limit_pre)) (PreH7 : (entering >= 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON_2 OD_2 )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (retval: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (retval = 0)) (PreH8 : (retval = 0)) (PreH9 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) retval ON_2 OD_2 )) (PreH10 : ((retval = 1) -> ((simplex_pivot_closed CN CD ON_2 OD_2 M_normal_state V_normal_state row entering (Znth (row) (CB) (0)) ) /\ (simplex_pivot_equiv CN CD ON_2 OD_2 CB M_normal_state V_normal_state row entering )))) (PreH11 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (ON_2) (0))) /\ ((Znth (k) (ON_2) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (OD_2) (1)))) /\ ((Znth (k) (OD_2) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (ON_2) (0))))) ((Znth (k) (OD_2) (1)))) = 1)))) (PreH12 : (count < pivot_limit_pre)) (PreH13 : (entering >= 0)) (PreH14 : (s_pre = S_normal_state)) (PreH15 : (pivot_limit_pre = L_normal_state)) (PreH16 : (0 <= M_normal_state)) (PreH17 : (M_normal_state <= 16)) (PreH18 : (0 <= I_normal_state)) (PreH19 : (I_normal_state <= 8)) (PreH20 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH21 : (0 <= V_normal_state)) (PreH22 : (V_normal_state <= 24)) (PreH23 : (0 <= L_normal_state)) (PreH24 : (L_normal_state <= INT_MAX)) (PreH25 : (0 <= count)) (PreH26 : (count <= L_normal_state)) (PreH27 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH28 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH30 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH31 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (retval)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) ((Znth (row) (CB) (0))) (entering) (retval)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state ON_2 OD_2 )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_4_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count >= pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (count >= pivot_limit_pre)) (PreH8 : (entering >= 0)) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH27 : (0 <= row)) (PreH28 : (row < M_normal_state)) (PreH29 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_5_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count >= pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (count >= pivot_limit_pre)) (PreH8 : (entering >= 0)) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH27 : (0 <= row)) (PreH28 : (row < M_normal_state)) (PreH29 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_6_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (entering < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH19 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (1 = 1) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state 1 ON OD OB OIB OVN OVD ) ”
  &&  “ ((1 <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((1 = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ ((1 = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (entering < 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state 1 ON OD OB OIB OVN OVD ) ”
  &&  “ ((1 <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((1 = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ ((1 = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_7_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (entering < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH19 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (1 = 1) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state 1 ON OD OB OIB OVN OVD ) ”
  &&  “ ((1 <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((1 = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ ((1 = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (entering < 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH25 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state 1 ON OD OB OIB OVN OVD ) ”
  &&  “ ((1 <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((1 = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ ((1 = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_8_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (M_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (M_normal_state >= INT_MIN)) (PreH6 : (V_normal_state >= INT_MIN)) (PreH7 : (retval = 0)) (PreH8 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_9_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (0 <= row)) (PreH21 : (row < M_normal_state)) (PreH22 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (e: Z) (retval: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (M_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (M_normal_state >= INT_MIN)) (PreH6 : (V_normal_state >= INT_MIN)) (PreH7 : (retval = 0)) (PreH8 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state retval e )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (0 <= row)) (PreH27 : (row < M_normal_state)) (PreH28 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_10_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (row < 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (0 = 0) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state 0 ON OD OB OIB OVN OVD ) ”
  &&  “ ((0 <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((0 = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ ((0 = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (row < 0)) (PreH8 : (s_pre = S_normal_state)) (PreH9 : (pivot_limit_pre = L_normal_state)) (PreH10 : (0 <= M_normal_state)) (PreH11 : (M_normal_state <= 16)) (PreH12 : (0 <= I_normal_state)) (PreH13 : (I_normal_state <= 8)) (PreH14 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH15 : (0 <= V_normal_state)) (PreH16 : (V_normal_state <= 24)) (PreH17 : (0 <= L_normal_state)) (PreH18 : (L_normal_state <= INT_MAX)) (PreH19 : (0 <= count)) (PreH20 : (count <= L_normal_state)) (PreH21 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH22 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH24 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state 0 ON OD OB OIB OVN OVD ) ”
  &&  “ ((0 <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((0 = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ ((0 = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_11_normal_state :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (R: Z) (D: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state retval R D )) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (R: Z) (D: Z) (retval: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (I_normal_state >= INT_MIN)) (PreH5 : (V_normal_state >= INT_MIN)) (PreH6 : (M_normal_state >= INT_MIN)) (PreH7 : (retval = 0)) (PreH8 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state retval R D )) (PreH9 : (s_pre = S_normal_state)) (PreH10 : (pivot_limit_pre = L_normal_state)) (PreH11 : (0 <= M_normal_state)) (PreH12 : (M_normal_state <= 16)) (PreH13 : (0 <= I_normal_state)) (PreH14 : (I_normal_state <= 8)) (PreH15 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH16 : (0 <= V_normal_state)) (PreH17 : (V_normal_state <= 24)) (PreH18 : (0 <= L_normal_state)) (PreH19 : (L_normal_state <= INT_MAX)) (PreH20 : (0 <= count)) (PreH21 : (count <= L_normal_state)) (PreH22 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH23 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH24 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON OD )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN OVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
).

Definition sx_solve_return_wit_12_negative_budget :=
forall (L_negative_budget: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre < 0)) (PreH2 : (pivot_limit_pre = L_negative_budget)) (PreH3 : ((INT_MIN) <= L_negative_budget)) (PreH4 : (L_negative_budget < 0)),
  TT && emp 
|--
  “ ((-1) = (-1)) ”
  &&  emp
.

Definition sx_solve_partial_solve_wit_1_normal_state_pure :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (s_pre = s_pre) ”
  &&  “ (( &( "row" ) ) = ( &( "row" ) )) ”
  &&  “ (( &( "direction" ) ) = ( &( "direction" ) )) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < V_normal_state))) ”
  &&  “ forall (j_4: Z), (((In j_4 CB ) /\ ((Znth (j_4) (HU_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_4) (UN_normal_state) (0))) /\ ((Znth (j_4) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_4) (UD_normal_state) (0)))) /\ ((Znth (j_4) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (j_3: Z), (((In j_3 CB ) /\ ((Znth (j_3) (HL_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_3) (LN_normal_state) (0))) /\ ((Znth (j_3) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_3) (LD_normal_state) (0)))) /\ ((Znth (j_3) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (j_2: Z), (((In j_2 CB ) /\ (((Znth (j_2) (HL_normal_state) (0)) <> 0) \/ ((Znth (j_2) (HU_normal_state) (0)) <> 0))) -> (((((INT_MIN) <= (Znth (j_2) (CVN) (0))) /\ ((Znth (j_2) (CVN) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_2) (CVD) (0)))) /\ ((Znth (j_2) (CVD) (0)) <= INT_MAX))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < (M_normal_state + I_normal_state )))) ”
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (pivot_limit_pre <= INT_MAX)) (PreH6 : (I_normal_state >= INT_MIN)) (PreH7 : (V_normal_state >= INT_MIN)) (PreH8 : (M_normal_state >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (pivot_limit_pre >= INT_MIN)) (PreH11 : (s_pre = S_normal_state)) (PreH12 : (pivot_limit_pre = L_normal_state)) (PreH13 : (0 <= M_normal_state)) (PreH14 : (M_normal_state <= 16)) (PreH15 : (0 <= I_normal_state)) (PreH16 : (I_normal_state <= 8)) (PreH17 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH18 : (0 <= V_normal_state)) (PreH19 : (V_normal_state <= 24)) (PreH20 : (0 <= L_normal_state)) (PreH21 : (L_normal_state <= INT_MAX)) (PreH22 : (0 <= count)) (PreH23 : (count <= L_normal_state)) (PreH24 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH25 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH26 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < (M_normal_state + I_normal_state )))) ”
  &&  “ forall (j_2: Z), (((In j_2 CB ) /\ (((Znth (j_2) (HL_normal_state) (0)) <> 0) \/ ((Znth (j_2) (HU_normal_state) (0)) <> 0))) -> (((((INT_MIN) <= (Znth (j_2) (CVN) (0))) /\ ((Znth (j_2) (CVN) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_2) (CVD) (0)))) /\ ((Znth (j_2) (CVD) (0)) <= INT_MAX))) ”
  &&  “ forall (j_3: Z), (((In j_3 CB ) /\ ((Znth (j_3) (HL_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_3) (LN_normal_state) (0))) /\ ((Znth (j_3) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_3) (LD_normal_state) (0)))) /\ ((Znth (j_3) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (j_4: Z), (((In j_4 CB ) /\ ((Znth (j_4) (HU_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_4) (UN_normal_state) (0))) /\ ((Znth (j_4) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_4) (UD_normal_state) (0)))) /\ ((Znth (j_4) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < V_normal_state))) ”
).

Definition sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (pivot_limit_pre <= INT_MAX)) (PreH6 : (I_normal_state >= INT_MIN)) (PreH7 : (V_normal_state >= INT_MIN)) (PreH8 : (M_normal_state >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (pivot_limit_pre >= INT_MIN)) (PreH11 : (s_pre = S_normal_state)) (PreH12 : (pivot_limit_pre = L_normal_state)) (PreH13 : (0 <= M_normal_state)) (PreH14 : (M_normal_state <= 16)) (PreH15 : (0 <= I_normal_state)) (PreH16 : (I_normal_state <= 8)) (PreH17 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH18 : (0 <= V_normal_state)) (PreH19 : (V_normal_state <= 24)) (PreH20 : (0 <= L_normal_state)) (PreH21 : (L_normal_state <= INT_MAX)) (PreH22 : (0 <= count)) (PreH23 : (count <= L_normal_state)) (PreH24 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH25 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH26 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < (M_normal_state + I_normal_state )))) ”
.

Definition sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_2 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (pivot_limit_pre <= INT_MAX)) (PreH6 : (I_normal_state >= INT_MIN)) (PreH7 : (V_normal_state >= INT_MIN)) (PreH8 : (M_normal_state >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (pivot_limit_pre >= INT_MIN)) (PreH11 : (s_pre = S_normal_state)) (PreH12 : (pivot_limit_pre = L_normal_state)) (PreH13 : (0 <= M_normal_state)) (PreH14 : (M_normal_state <= 16)) (PreH15 : (0 <= I_normal_state)) (PreH16 : (I_normal_state <= 8)) (PreH17 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH18 : (0 <= V_normal_state)) (PreH19 : (V_normal_state <= 24)) (PreH20 : (0 <= L_normal_state)) (PreH21 : (L_normal_state <= INT_MAX)) (PreH22 : (0 <= count)) (PreH23 : (count <= L_normal_state)) (PreH24 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH25 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH26 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (j_2: Z), (((In j_2 CB ) /\ (((Znth (j_2) (HL_normal_state) (0)) <> 0) \/ ((Znth (j_2) (HU_normal_state) (0)) <> 0))) -> (((((INT_MIN) <= (Znth (j_2) (CVN) (0))) /\ ((Znth (j_2) (CVN) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_2) (CVD) (0)))) /\ ((Znth (j_2) (CVD) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_3 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (pivot_limit_pre <= INT_MAX)) (PreH6 : (I_normal_state >= INT_MIN)) (PreH7 : (V_normal_state >= INT_MIN)) (PreH8 : (M_normal_state >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (pivot_limit_pre >= INT_MIN)) (PreH11 : (s_pre = S_normal_state)) (PreH12 : (pivot_limit_pre = L_normal_state)) (PreH13 : (0 <= M_normal_state)) (PreH14 : (M_normal_state <= 16)) (PreH15 : (0 <= I_normal_state)) (PreH16 : (I_normal_state <= 8)) (PreH17 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH18 : (0 <= V_normal_state)) (PreH19 : (V_normal_state <= 24)) (PreH20 : (0 <= L_normal_state)) (PreH21 : (L_normal_state <= INT_MAX)) (PreH22 : (0 <= count)) (PreH23 : (count <= L_normal_state)) (PreH24 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH25 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH26 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (j_3: Z), (((In j_3 CB ) /\ ((Znth (j_3) (HL_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_3) (LN_normal_state) (0))) /\ ((Znth (j_3) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_3) (LD_normal_state) (0)))) /\ ((Znth (j_3) (LD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_4 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (pivot_limit_pre <= INT_MAX)) (PreH6 : (I_normal_state >= INT_MIN)) (PreH7 : (V_normal_state >= INT_MIN)) (PreH8 : (M_normal_state >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (pivot_limit_pre >= INT_MIN)) (PreH11 : (s_pre = S_normal_state)) (PreH12 : (pivot_limit_pre = L_normal_state)) (PreH13 : (0 <= M_normal_state)) (PreH14 : (M_normal_state <= 16)) (PreH15 : (0 <= I_normal_state)) (PreH16 : (I_normal_state <= 8)) (PreH17 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH18 : (0 <= V_normal_state)) (PreH19 : (V_normal_state <= 24)) (PreH20 : (0 <= L_normal_state)) (PreH21 : (L_normal_state <= INT_MAX)) (PreH22 : (0 <= count)) (PreH23 : (count <= L_normal_state)) (PreH24 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH25 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH26 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (j_4: Z), (((In j_4 CB ) /\ ((Znth (j_4) (HU_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_4) (UN_normal_state) (0))) /\ ((Znth (j_4) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_4) (UD_normal_state) (0)))) /\ ((Znth (j_4) (UD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_1_normal_state_pure_split_goal_5 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (count <= INT_MAX)) (PreH5 : (pivot_limit_pre <= INT_MAX)) (PreH6 : (I_normal_state >= INT_MIN)) (PreH7 : (V_normal_state >= INT_MIN)) (PreH8 : (M_normal_state >= INT_MIN)) (PreH9 : (count >= INT_MIN)) (PreH10 : (pivot_limit_pre >= INT_MIN)) (PreH11 : (s_pre = S_normal_state)) (PreH12 : (pivot_limit_pre = L_normal_state)) (PreH13 : (0 <= M_normal_state)) (PreH14 : (M_normal_state <= 16)) (PreH15 : (0 <= I_normal_state)) (PreH16 : (I_normal_state <= 8)) (PreH17 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH18 : (0 <= V_normal_state)) (PreH19 : (V_normal_state <= 24)) (PreH20 : (0 <= L_normal_state)) (PreH21 : (L_normal_state <= INT_MAX)) (PreH22 : (0 <= count)) (PreH23 : (count <= L_normal_state)) (PreH24 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH25 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH26 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "row" ) )) # Int  |->_)
  **  ((( &( "direction" ) )) # Int  |->_)
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < V_normal_state))) ”
.

Definition sx_solve_partial_solve_wit_1_normal_state_aux :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (s_pre = s_pre) ”
  &&  “ (( &( "row" ) ) = ( &( "row" ) )) ”
  &&  “ (( &( "direction" ) ) = ( &( "direction" ) )) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < V_normal_state))) ”
  &&  “ forall (j_4: Z), (((In j_4 CB ) /\ ((Znth (j_4) (HU_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_4) (UN_normal_state) (0))) /\ ((Znth (j_4) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_4) (UD_normal_state) (0)))) /\ ((Znth (j_4) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (j_3: Z), (((In j_3 CB ) /\ ((Znth (j_3) (HL_normal_state) (0)) <> 0)) -> (((((INT_MIN) <= (Znth (j_3) (LN_normal_state) (0))) /\ ((Znth (j_3) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_3) (LD_normal_state) (0)))) /\ ((Znth (j_3) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (j_2: Z), (((In j_2 CB ) /\ (((Znth (j_2) (HL_normal_state) (0)) <> 0) \/ ((Znth (j_2) (HU_normal_state) (0)) <> 0))) -> (((((INT_MIN) <= (Znth (j_2) (CVN) (0))) /\ ((Znth (j_2) (CVN) (0)) <= INT_MAX)) /\ (1 <= (Znth (j_2) (CVD) (0)))) /\ ((Znth (j_2) (CVD) (0)) <= INT_MAX))) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < M_normal_state)) -> ((0 <= (Znth (j) (CB) (0))) /\ ((Znth (j) (CB) (0)) < (M_normal_state + I_normal_state )))) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_scan_read_memory s_pre CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_read_rest s_pre V_normal_state CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
.

Definition sx_solve_partial_solve_wit_1_normal_state := sx_solve_partial_solve_wit_1_normal_state_pure -> sx_solve_partial_solve_wit_1_normal_state_aux.

Definition sx_solve_partial_solve_wit_2_normal_state_pure :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (direction = direction) ”
  &&  “ (( &( "entering" ) ) = ( &( "entering" ) )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < 16) ”
  &&  “ ((INT_MIN) <= row) ”
  &&  “ (row <= INT_MAX) ”
  &&  “ ((INT_MIN) <= direction) ”
  &&  “ (direction <= INT_MAX) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = V_normal_state) ”
  &&  “ ((Zlength (CVN)) = V_normal_state) ”
  &&  “ ((Zlength (CVD)) = V_normal_state) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
  &&  “ (Forall (Z.le (1)) CVD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
  &&  “ (Forall (Z.le (1)) CVD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
).

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_2 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_3 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_4 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_5 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_6 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_7 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_8 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.le (1)) CVD ) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_9 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_10 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_11 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_12 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_13 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_14 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_15 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_pure_split_goal_16 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = 1)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_2_normal_state_aux :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (direction = direction) ”
  &&  “ (( &( "entering" ) ) = ( &( "entering" ) )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < 16) ”
  &&  “ ((INT_MIN) <= row) ”
  &&  “ (row <= INT_MAX) ”
  &&  “ ((INT_MIN) <= direction) ”
  &&  “ (direction <= INT_MAX) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = V_normal_state) ”
  &&  “ ((Zlength (CVN)) = V_normal_state) ”
  &&  “ ((Zlength (CVD)) = V_normal_state) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
  &&  “ (Forall (Z.le (1)) CVD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = 1) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
.

Definition sx_solve_partial_solve_wit_2_normal_state := sx_solve_partial_solve_wit_2_normal_state_pure -> sx_solve_partial_solve_wit_2_normal_state_aux.

Definition sx_solve_partial_solve_wit_3_normal_state_pure :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (direction = direction) ”
  &&  “ (( &( "entering" ) ) = ( &( "entering" ) )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < 16) ”
  &&  “ ((INT_MIN) <= row) ”
  &&  “ (row <= INT_MAX) ”
  &&  “ ((INT_MIN) <= direction) ”
  &&  “ (direction <= INT_MAX) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = V_normal_state) ”
  &&  “ ((Zlength (CVN)) = V_normal_state) ”
  &&  “ ((Zlength (CVD)) = V_normal_state) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
  &&  “ (Forall (Z.le (1)) CVD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
  &&  “ (Forall (Z.le (1)) CVD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
).

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_2 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_3 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_4 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_5 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_6 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_7 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_8 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.le (1)) CVD ) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_9 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_10 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_11 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_12 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_13 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_14 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_15 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_pure_split_goal_16 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (row <= INT_MAX)) (PreH5 : (direction <= INT_MAX)) (PreH6 : (count <= INT_MAX)) (PreH7 : (pivot_limit_pre <= INT_MAX)) (PreH8 : (I_normal_state >= INT_MIN)) (PreH9 : (V_normal_state >= INT_MIN)) (PreH10 : (M_normal_state >= INT_MIN)) (PreH11 : (row >= INT_MIN)) (PreH12 : (direction >= INT_MIN)) (PreH13 : (count >= INT_MIN)) (PreH14 : (pivot_limit_pre >= INT_MIN)) (PreH15 : (s_pre = S_normal_state)) (PreH16 : (pivot_limit_pre = L_normal_state)) (PreH17 : (0 <= M_normal_state)) (PreH18 : (M_normal_state <= 16)) (PreH19 : (0 <= I_normal_state)) (PreH20 : (I_normal_state <= 8)) (PreH21 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH22 : (0 <= V_normal_state)) (PreH23 : (V_normal_state <= 24)) (PreH24 : (0 <= L_normal_state)) (PreH25 : (L_normal_state <= INT_MAX)) (PreH26 : (0 <= count)) (PreH27 : (count <= L_normal_state)) (PreH28 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH29 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH30 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH31 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH32 : (0 <= row)) (PreH33 : (row < M_normal_state)) (PreH34 : (direction = (-1))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
  **  ((( &( "entering" ) )) # Int  |->_)
  **  ((( &( "leaving" ) )) # Int  |->_)
|--
  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_3_normal_state_aux :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) (V_normal_state)) )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (direction = direction) ”
  &&  “ (( &( "entering" ) ) = ( &( "entering" ) )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < 16) ”
  &&  “ ((INT_MIN) <= row) ”
  &&  “ (row <= INT_MAX) ”
  &&  “ ((INT_MIN) <= direction) ”
  &&  “ (direction <= INT_MAX) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = V_normal_state) ”
  &&  “ ((Zlength (CVN)) = V_normal_state) ”
  &&  “ ((Zlength (CVD)) = V_normal_state) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < V_normal_state)) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < V_normal_state)) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i_2: Z), ((((0 <= i_2) /\ (i_2 < (M_normal_state + I_normal_state ))) /\ ((Znth (i_2) (HU_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i_2) (UN_normal_state) (0))) /\ ((Znth (i_2) (UN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i_2) (UD_normal_state) (0)))) /\ ((Znth (i_2) (UD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ forall (i: Z), ((((0 <= i) /\ (i < (M_normal_state + I_normal_state ))) /\ ((Znth (i) (HL_normal_state) (0)) <> 0)) -> (((((-INT_MAX) <= (Znth (i) (LN_normal_state) (0))) /\ ((Znth (i) (LN_normal_state) (0)) <= INT_MAX)) /\ (1 <= (Znth (i) (LD_normal_state) (0)))) /\ ((Znth (i) (LD_normal_state) (0)) <= INT_MAX))) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVD ) ”
  &&  “ (Forall (Z.le (1)) CVD ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) CVN ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) CVN ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ ((Zlength (CVD)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CVN)) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))))) = (M_normal_state + I_normal_state )) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = (-1)) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_scan_read_memory s_pre (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_enter_num_memory s_pre row V_normal_state (simplex_solve_row (CN) (row) ((M_normal_state + I_normal_state ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (simplex_solve_read_rest s_pre V_normal_state (Zrange (0) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  (simplex_solve_enter_rest s_pre M_normal_state V_normal_state CN CD row )
.

Definition sx_solve_partial_solve_wit_3_normal_state := sx_solve_partial_solve_wit_3_normal_state_pure -> sx_solve_partial_solve_wit_3_normal_state_aux.

Definition sx_solve_partial_solve_wit_4_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count < pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = 1)),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (count < pivot_limit_pre) ”
  &&  “ (entering >= 0) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = 1) ”
  &&  (((&((s_pre)  # "SxState" ->ₛ "basic") + (row * sizeof(INT)))) # Int  |-> (Znth row CB 0))
  **  (IntArray.missing_i &((s_pre)  # "SxState" ->ₛ "basic") row 0 M_normal_state CB )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
.

Definition sx_solve_partial_solve_wit_5_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count < pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = (-1))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (count < pivot_limit_pre) ”
  &&  “ (entering >= 0) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = (-1)) ”
  &&  (((&((s_pre)  # "SxState" ->ₛ "basic") + (row * sizeof(INT)))) # Int  |-> (Znth row CB 0))
  **  (IntArray.missing_i &((s_pre)  # "SxState" ->ₛ "basic") row 0 M_normal_state CB )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count < pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (entering = entering) ”
  &&  “ (1 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (1 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
  &&  “ ((Znth (entering) (CIB) (0)) = 0) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ (NoDup CB ) ”
  &&  “ ((Zlength (CD)) = 400) ”
  &&  “ ((Zlength (CN)) = 400) ”
  &&  “ (entering < (M_normal_state + I_normal_state )) ”
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (entering < (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CN)) = 400) ”
  &&  “ ((Zlength (CD)) = 400) ”
  &&  “ (NoDup CB ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ ((Znth (entering) (CIB) (0)) = 0) ”
  &&  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ (entering < (M_normal_state + I_normal_state )) ”
).

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (entering < (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_2 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ ((Zlength (CN)) = 400) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_3 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ ((Zlength (CD)) = 400) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_4 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (NoDup CB ) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_5 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_6 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_7 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ ((Znth (entering) (CIB) (0)) = 0) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_8 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_9 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_10 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_11 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_12 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_pure_split_goal_13 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (entering < (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_6_normal_state_aux :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count < pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = 1)),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (entering = entering) ”
  &&  “ (1 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (1 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
  &&  “ ((Znth (entering) (CIB) (0)) = 0) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ (NoDup CB ) ”
  &&  “ ((Zlength (CD)) = 400) ”
  &&  “ ((Zlength (CN)) = 400) ”
  &&  “ (entering < (M_normal_state + I_normal_state )) ”
  &&  “ (count < pivot_limit_pre) ”
  &&  “ (entering >= 0) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = 1) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
.

Definition sx_solve_partial_solve_wit_6_normal_state := sx_solve_partial_solve_wit_6_normal_state_pure -> sx_solve_partial_solve_wit_6_normal_state_aux.

Definition sx_solve_partial_solve_wit_7_normal_state_pure :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count < pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (entering = entering) ”
  &&  “ (1 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (1 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
  &&  “ ((Znth (entering) (CIB) (0)) = 0) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ (NoDup CB ) ”
  &&  “ ((Zlength (CD)) = 400) ”
  &&  “ ((Zlength (CN)) = 400) ”
  &&  “ (entering < (M_normal_state + I_normal_state )) ”
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (entering < (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength (CN)) = 400) ”
  &&  “ ((Zlength (CD)) = 400) ”
  &&  “ (NoDup CB ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ ((Znth (entering) (CIB) (0)) = 0) ”
  &&  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ (entering < (M_normal_state + I_normal_state )) ”
).

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (entering < (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_2 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ ((Zlength (CN)) = 400) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_3 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ ((Zlength (CD)) = 400) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_4 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (NoDup CB ) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_5 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_6 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_7 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ ((Znth (entering) (CIB) (0)) = 0) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_8 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_9 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_10 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_11 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_12 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_pure_split_goal_13 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : ((Znth row CB 0) <= INT_MAX)) (PreH2 : (I_normal_state <= INT_MAX)) (PreH3 : (V_normal_state <= INT_MAX)) (PreH4 : (M_normal_state <= INT_MAX)) (PreH5 : (entering <= INT_MAX)) (PreH6 : (row <= INT_MAX)) (PreH7 : (direction <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : ((Znth row CB 0) >= INT_MIN)) (PreH11 : (I_normal_state >= INT_MIN)) (PreH12 : (V_normal_state >= INT_MIN)) (PreH13 : (M_normal_state >= INT_MIN)) (PreH14 : (entering >= INT_MIN)) (PreH15 : (row >= INT_MIN)) (PreH16 : (direction >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (count < pivot_limit_pre)) (PreH20 : (entering >= 0)) (PreH21 : (s_pre = S_normal_state)) (PreH22 : (pivot_limit_pre = L_normal_state)) (PreH23 : (0 <= M_normal_state)) (PreH24 : (M_normal_state <= 16)) (PreH25 : (0 <= I_normal_state)) (PreH26 : (I_normal_state <= 8)) (PreH27 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH28 : (0 <= V_normal_state)) (PreH29 : (V_normal_state <= 24)) (PreH30 : (0 <= L_normal_state)) (PreH31 : (L_normal_state <= INT_MAX)) (PreH32 : (0 <= count)) (PreH33 : (count <= L_normal_state)) (PreH34 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH35 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH36 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH37 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH38 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH39 : (0 <= row)) (PreH40 : (row < M_normal_state)) (PreH41 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
  **  ((( &( "leaving" ) )) # Int  |-> (Znth row CB 0))
|--
  “ (entering < (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_7_normal_state_aux :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (count: Z) (direction: Z) (row: Z) (entering: Z) (PreH1 : (count < pivot_limit_pre)) (PreH2 : (entering >= 0)) (PreH3 : (s_pre = S_normal_state)) (PreH4 : (pivot_limit_pre = L_normal_state)) (PreH5 : (0 <= M_normal_state)) (PreH6 : (M_normal_state <= 16)) (PreH7 : (0 <= I_normal_state)) (PreH8 : (I_normal_state <= 8)) (PreH9 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH10 : (0 <= V_normal_state)) (PreH11 : (V_normal_state <= 24)) (PreH12 : (0 <= L_normal_state)) (PreH13 : (L_normal_state <= INT_MAX)) (PreH14 : (0 <= count)) (PreH15 : (count <= L_normal_state)) (PreH16 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH18 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH19 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH20 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH21 : (0 <= row)) (PreH22 : (row < M_normal_state)) (PreH23 : (direction = (-1))),
  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (s_pre = s_pre) ”
  &&  “ (row = row) ”
  &&  “ (entering = entering) ”
  &&  “ (1 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (1 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < V_normal_state)) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < V_normal_state)) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (k_4: Z), ((In k_4 (simplex_pivot_slots (M_normal_state) ((M_normal_state + I_normal_state ))) ) -> ((((((-INT_MAX) <= (Znth (k_4) (CN) (0))) /\ ((Znth (k_4) (CN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_4) (CD) (1)))) /\ ((Znth (k_4) (CD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_4) (CN) (0))))) ((Znth (k_4) (CD) (1)))) = 1))) ”
  &&  “ forall (i: Z), forall (k_3: Z), (((((0 <= i) /\ (i < M_normal_state)) /\ (0 <= k_3)) /\ (k_3 < M_normal_state)) -> ((Znth (((16 + (i * 24 ) ) + (Znth (k_3) (CB) (0)) )) (CN) (0)) = 0)) ”
  &&  “ ((Znth (entering) (CIB) (0)) = 0) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (M_normal_state + I_normal_state ))) -> (((0 <= (Znth (k_2) (CIB) (0))) /\ ((Znth (k_2) (CIB) (0)) <= 1)) /\ (((Znth (k_2) (CIB) (0)) <> 0) -> (In k_2 CB )))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> (((0 <= (Znth (k) (CB) (0))) /\ ((Znth (k) (CB) (0)) < (M_normal_state + I_normal_state ))) /\ ((Znth ((Znth (k) (CB) (0))) (CIB) (0)) = 1))) ”
  &&  “ (NoDup CB ) ”
  &&  “ ((Zlength (CD)) = 400) ”
  &&  “ ((Zlength (CN)) = 400) ”
  &&  “ (entering < (M_normal_state + I_normal_state )) ”
  &&  “ (count < pivot_limit_pre) ”
  &&  “ (entering >= 0) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (direction = (-1)) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state CB )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state CIB )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state CN CD )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
.

Definition sx_solve_partial_solve_wit_7_normal_state := sx_solve_partial_solve_wit_7_normal_state_pure -> sx_solve_partial_solve_wit_7_normal_state_aux.

Definition sx_solve_partial_solve_wit_8_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (direction > 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (0 <= entering)) (PreH21 : (entering < V_normal_state)) (PreH22 : (0 <= leaving)) (PreH23 : (leaving < V_normal_state)) (PreH24 : (leaving = (Znth (row) (CB) (0)))) (PreH25 : (count < L_normal_state)) (PreH26 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH27 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH28 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH29 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH30 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH31 : ((Zlength (PN)) = 400)) (PreH32 : ((Zlength (PD)) = 400)) (PreH33 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  (UndefStructPredSxRat (&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  “ (direction > 0) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
.

Definition sx_solve_partial_solve_wit_9_normal_state :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (direction <= 0)) (PreH2 : (s_pre = S_normal_state)) (PreH3 : (pivot_limit_pre = L_normal_state)) (PreH4 : (0 <= M_normal_state)) (PreH5 : (M_normal_state <= 16)) (PreH6 : (0 <= I_normal_state)) (PreH7 : (I_normal_state <= 8)) (PreH8 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH9 : (0 <= V_normal_state)) (PreH10 : (V_normal_state <= 24)) (PreH11 : (0 <= L_normal_state)) (PreH12 : (L_normal_state <= INT_MAX)) (PreH13 : (0 <= count)) (PreH14 : (count <= L_normal_state)) (PreH15 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH17 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH18 : (0 <= row)) (PreH19 : (row < M_normal_state)) (PreH20 : (0 <= entering)) (PreH21 : (entering < V_normal_state)) (PreH22 : (0 <= leaving)) (PreH23 : (leaving < V_normal_state)) (PreH24 : (leaving = (Znth (row) (CB) (0)))) (PreH25 : (count < L_normal_state)) (PreH26 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH27 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH28 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH29 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH30 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH31 : ((Zlength (PN)) = 400)) (PreH32 : ((Zlength (PD)) = 400)) (PreH33 : forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1)))),
  (UndefStructPredSxRat (&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))) )
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
|--
  “ (direction <= 0) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k: Z), ((In k (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k) (PN) (0))) /\ ((Znth (k) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k) (PD) (1)))) /\ ((Znth (k) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k) (PN) (0))))) ((Znth (k) (PD) (1)))) = 1))) ”
  &&  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (UD_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "value") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "upper") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (UN_normal_state) (0)))
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state PN PD )
  **  (simplex_recompute_values_except s_pre V_normal_state CVN CVD leaving )
  **  (simplex_solve_bound_except s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state leaving )
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth (leaving) (LN_normal_state) (0)))
  **  ((&(((&((s_pre)  # "SxState" ->ₛ "lower") + (leaving * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> (Znth (leaving) (LD_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_lower") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HL_normal_state) (0)))
  **  (((&((s_pre)  # "SxState" ->ₛ "has_upper") + (leaving * sizeof(INT)))) # Int  |-> (Znth (leaving) (HU_normal_state) (0)))
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure :=
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (0 <= row)) (PreH18 : (row < M_normal_state)) (PreH19 : (0 <= entering)) (PreH20 : (entering < V_normal_state)) (PreH21 : (0 <= leaving)) (PreH22 : (leaving < V_normal_state)) (PreH23 : (leaving = (Znth (row) (CB) (0)))) (PreH24 : (count < L_normal_state)) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH27 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH28 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH29 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH30 : ((Zlength (PN)) = 400)) (PreH31 : ((Zlength (PD)) = 400)) (PreH32 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (s_pre = s_pre) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < V_normal_state))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)))) = V_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)))) = V_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < (M_normal_state + I_normal_state )))) ”
  &&  “ ((Zlength ((simplex_solve_rhs (PD) (M_normal_state)))) = M_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_rhs (PN) (M_normal_state)))) = M_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
  &&  “ ((Zlength ((simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
) \/
(
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
  &&  “ ((Zlength ((simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
  &&  “ ((Zlength ((simplex_solve_rhs (PN) (M_normal_state)))) = M_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_rhs (PD) (M_normal_state)))) = M_normal_state) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < (M_normal_state + I_normal_state )))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < V_normal_state))) ”
).

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_1 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_2 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_3 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_rhs (PN) (M_normal_state)))) = M_normal_state) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_4 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_rhs (PD) (M_normal_state)))) = M_normal_state) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_5 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < (M_normal_state + I_normal_state )))) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_6 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_7 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_8 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le (1)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_9 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_10 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_11 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_12 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le (1)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_13 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_14 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_15 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_16 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_17 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_18 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_19 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_20 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_21 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_22 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_23 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_24 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_25 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_pure_split_goal_26 :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (I_normal_state <= INT_MAX)) (PreH2 : (V_normal_state <= INT_MAX)) (PreH3 : (M_normal_state <= INT_MAX)) (PreH4 : (direction <= INT_MAX)) (PreH5 : (leaving <= INT_MAX)) (PreH6 : (entering <= INT_MAX)) (PreH7 : (row <= INT_MAX)) (PreH8 : (count <= INT_MAX)) (PreH9 : (pivot_limit_pre <= INT_MAX)) (PreH10 : (I_normal_state >= INT_MIN)) (PreH11 : (V_normal_state >= INT_MIN)) (PreH12 : (M_normal_state >= INT_MIN)) (PreH13 : (direction >= INT_MIN)) (PreH14 : (leaving >= INT_MIN)) (PreH15 : (entering >= INT_MIN)) (PreH16 : (row >= INT_MIN)) (PreH17 : (count >= INT_MIN)) (PreH18 : (pivot_limit_pre >= INT_MIN)) (PreH19 : (s_pre = S_normal_state)) (PreH20 : (pivot_limit_pre = L_normal_state)) (PreH21 : (0 <= M_normal_state)) (PreH22 : (M_normal_state <= 16)) (PreH23 : (0 <= I_normal_state)) (PreH24 : (I_normal_state <= 8)) (PreH25 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH26 : (0 <= V_normal_state)) (PreH27 : (V_normal_state <= 24)) (PreH28 : (0 <= L_normal_state)) (PreH29 : (L_normal_state <= INT_MAX)) (PreH30 : (0 <= count)) (PreH31 : (count <= L_normal_state)) (PreH32 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH33 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH34 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH35 : (0 <= row)) (PreH36 : (row < M_normal_state)) (PreH37 : (0 <= entering)) (PreH38 : (entering < V_normal_state)) (PreH39 : (0 <= leaving)) (PreH40 : (leaving < V_normal_state)) (PreH41 : (leaving = (Znth (row) (CB) (0)))) (PreH42 : (count < L_normal_state)) (PreH43 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH44 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH45 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH46 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH47 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH48 : ((Zlength (PN)) = 400)) (PreH49 : ((Zlength (PD)) = 400)) (PreH50 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "row" ) )) # Int  |-> row)
  **  ((( &( "entering" ) )) # Int  |-> entering)
  **  ((( &( "leaving" ) )) # Int  |-> leaving)
  **  ((( &( "direction" ) )) # Int  |-> direction)
  **  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < V_normal_state))) ”
.

Definition sx_solve_partial_solve_wit_10_normal_state_aux :=
forall (VD_normal_state: (@list Z)) (VN_normal_state: (@list Z)) (UD_normal_state: (@list Z)) (UN_normal_state: (@list Z)) (LD_normal_state: (@list Z)) (LN_normal_state: (@list Z)) (HU_normal_state: (@list Z)) (HL_normal_state: (@list Z)) (IB_normal_state: (@list Z)) (B_normal_state: (@list Z)) (D_normal_state: (@list Z)) (N_normal_state: (@list Z)) (A_normal_state: (@list Z)) (V_normal_state: Z) (I_normal_state: Z) (M_normal_state: Z) (L_normal_state: Z) (S_normal_state: Z) (s_pre: Z) (pivot_limit_pre: Z) (CN: (@list Z)) (CD: (@list Z)) (CB: (@list Z)) (CIB: (@list Z)) (CVN: (@list Z)) (CVD: (@list Z)) (PN: (@list Z)) (PD: (@list Z)) (count: Z) (row: Z) (entering: Z) (leaving: Z) (direction: Z) (PreH1 : (s_pre = S_normal_state)) (PreH2 : (pivot_limit_pre = L_normal_state)) (PreH3 : (0 <= M_normal_state)) (PreH4 : (M_normal_state <= 16)) (PreH5 : (0 <= I_normal_state)) (PreH6 : (I_normal_state <= 8)) (PreH7 : (V_normal_state = (M_normal_state + I_normal_state ))) (PreH8 : (0 <= V_normal_state)) (PreH9 : (V_normal_state <= 24)) (PreH10 : (0 <= L_normal_state)) (PreH11 : (L_normal_state <= INT_MAX)) (PreH12 : (0 <= count)) (PreH13 : (count <= L_normal_state)) (PreH14 : (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH15 : (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) )) (PreH16 : (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD )) (PreH17 : (0 <= row)) (PreH18 : (row < M_normal_state)) (PreH19 : (0 <= entering)) (PreH20 : (entering < V_normal_state)) (PreH21 : (0 <= leaving)) (PreH22 : (leaving < V_normal_state)) (PreH23 : (leaving = (Znth (row) (CB) (0)))) (PreH24 : (count < L_normal_state)) (PreH25 : (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction )) (PreH26 : (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering )) (PreH27 : (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD )) (PreH28 : (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving )) (PreH29 : (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering )) (PreH30 : ((Zlength (PN)) = 400)) (PreH31 : ((Zlength (PD)) = 400)) (PreH32 : forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1)))),
  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) (V_normal_state)) (simplex_solve_matrix (1) (PD) (M_normal_state) (V_normal_state)) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) )
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
|--
  “ (s_pre = s_pre) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < V_normal_state))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) ) ”
  &&  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)))) = V_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)))) = V_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ ((Zlength ((simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)))) = (M_normal_state + I_normal_state )) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) (leaving) (direction)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_rhs (PD) (M_normal_state)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_rhs (PN) (M_normal_state)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) ) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_normal_state)) -> ((0 <= (Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0))) /\ ((Znth (k) ((simplex_pivot_basis (CB) (row) (entering) (1))) (0)) < (M_normal_state + I_normal_state )))) ”
  &&  “ ((Zlength ((simplex_solve_rhs (PD) (M_normal_state)))) = M_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_rhs (PN) (M_normal_state)))) = M_normal_state) ”
  &&  “ ((Zlength ((simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
  &&  “ ((Zlength ((simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))))) = (M_normal_state * 24 )) ”
  &&  “ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= count) ”
  &&  “ (count <= L_normal_state) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (CN) (CD) (CB) (CIB) (CVN) (CVD)) ) ”
  &&  “ (simplex_solve_progress HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state count N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state CN CD CB CIB CVN CVD ) ”
  &&  “ (0 <= row) ”
  &&  “ (row < M_normal_state) ”
  &&  “ (0 <= entering) ”
  &&  “ (entering < V_normal_state) ”
  &&  “ (0 <= leaving) ”
  &&  “ (leaving < V_normal_state) ”
  &&  “ (leaving = (Znth (row) (CB) (0))) ”
  &&  “ (count < L_normal_state) ”
  &&  “ (simplex_find_violation_spec CB HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state V_normal_state M_normal_state 1 row direction ) ”
  &&  “ (simplex_find_entering_spec CIB (simplex_solve_row (CN) (row) (V_normal_state)) HL_normal_state HU_normal_state CVN CVD LN_normal_state LD_normal_state UN_normal_state UD_normal_state direction V_normal_state 1 entering ) ”
  &&  “ (simplex_pivot_result CN CD M_normal_state V_normal_state row entering leaving 1 PN PD ) ”
  &&  “ (simplex_pivot_closed CN CD PN PD M_normal_state V_normal_state row entering leaving ) ”
  &&  “ (simplex_pivot_equiv CN CD PN PD CB M_normal_state V_normal_state row entering ) ”
  &&  “ ((Zlength (PN)) = 400) ”
  &&  “ ((Zlength (PD)) = 400) ”
  &&  “ forall (k_2: Z), ((In k_2 (simplex_pivot_slots (M_normal_state) (V_normal_state)) ) -> ((((((-INT_MAX) <= (Znth (k_2) (PN) (0))) /\ ((Znth (k_2) (PN) (0)) <= INT_MAX)) /\ (1 <= (Znth (k_2) (PD) (1)))) /\ ((Znth (k_2) (PD) (1)) <= INT_MAX)) /\ ((Zgcd ((Zabs ((Znth (k_2) (PN) (0))))) ((Znth (k_2) (PD) (1)))) = 1))) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state (simplex_pivot_basis (CB) (row) (entering) (1)) )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state (simplex_pivot_marks (CIB) (leaving) (entering) (1)) )
  **  (simplex_recompute_rhs s_pre M_normal_state (simplex_solve_rhs (PN) (M_normal_state)) (simplex_solve_rhs (PD) (M_normal_state)) )
  **  (simplex_recompute_matrix s_pre M_normal_state V_normal_state (simplex_solve_matrix (0) (PN) (M_normal_state) ((M_normal_state + I_normal_state ))) (simplex_solve_matrix (1) (PD) (M_normal_state) ((M_normal_state + I_normal_state ))) )
  **  (simplex_recompute_values s_pre V_normal_state (simplex_solve_repair (LN_normal_state) (UN_normal_state) (CVN) ((Znth (row) (CB) (0))) (direction)) (simplex_solve_repair (LD_normal_state) (UD_normal_state) (CVD) ((Znth (row) (CB) (0))) (direction)) )
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (simplex_solve_bound_memory s_pre V_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state )
.

Definition sx_solve_partial_solve_wit_10_normal_state := sx_solve_partial_solve_wit_10_normal_state_pure -> sx_solve_partial_solve_wit_10_normal_state_aux.

Module Type VC_Correct.


Axiom proof_of_sx_solve_safety_wit_1_negative_budget : sx_solve_safety_wit_1_negative_budget.
Axiom proof_of_sx_solve_safety_wit_2_normal_state : sx_solve_safety_wit_2_normal_state.
Axiom proof_of_sx_solve_safety_wit_3_negative_budget : sx_solve_safety_wit_3_negative_budget.
Axiom proof_of_sx_solve_safety_wit_4_normal_state : sx_solve_safety_wit_4_normal_state.
Axiom proof_of_sx_solve_safety_wit_5_negative_budget : sx_solve_safety_wit_5_negative_budget.
Axiom proof_of_sx_solve_safety_wit_6_normal_state : sx_solve_safety_wit_6_normal_state.
Axiom proof_of_sx_solve_safety_wit_7_negative_budget : sx_solve_safety_wit_7_negative_budget.
Axiom proof_of_sx_solve_safety_wit_8_negative_budget : sx_solve_safety_wit_8_negative_budget.
Axiom proof_of_sx_solve_safety_wit_9_normal_state : sx_solve_safety_wit_9_normal_state.
Axiom proof_of_sx_solve_safety_wit_10_normal_state : sx_solve_safety_wit_10_normal_state.
Axiom proof_of_sx_solve_safety_wit_11_normal_state : sx_solve_safety_wit_11_normal_state.
Axiom proof_of_sx_solve_safety_wit_12_normal_state : sx_solve_safety_wit_12_normal_state.
Axiom proof_of_sx_solve_safety_wit_13_normal_state : sx_solve_safety_wit_13_normal_state.
Axiom proof_of_sx_solve_safety_wit_14_normal_state : sx_solve_safety_wit_14_normal_state.
Axiom proof_of_sx_solve_safety_wit_15_normal_state : sx_solve_safety_wit_15_normal_state.
Axiom proof_of_sx_solve_safety_wit_16_normal_state : sx_solve_safety_wit_16_normal_state.
Axiom proof_of_sx_solve_safety_wit_17_normal_state : sx_solve_safety_wit_17_normal_state.
Axiom proof_of_sx_solve_safety_wit_18_normal_state : sx_solve_safety_wit_18_normal_state.
Axiom proof_of_sx_solve_safety_wit_19_normal_state : sx_solve_safety_wit_19_normal_state.
Axiom proof_of_sx_solve_safety_wit_20_normal_state : sx_solve_safety_wit_20_normal_state.
Axiom proof_of_sx_solve_safety_wit_21_normal_state : sx_solve_safety_wit_21_normal_state.
Axiom proof_of_sx_solve_safety_wit_22_normal_state : sx_solve_safety_wit_22_normal_state.
Axiom proof_of_sx_solve_safety_wit_23_normal_state : sx_solve_safety_wit_23_normal_state.
Axiom proof_of_sx_solve_safety_wit_24_normal_state : sx_solve_safety_wit_24_normal_state.
Axiom proof_of_sx_solve_safety_wit_25_normal_state : sx_solve_safety_wit_25_normal_state.
Axiom proof_of_sx_solve_safety_wit_26_normal_state : sx_solve_safety_wit_26_normal_state.
Axiom proof_of_sx_solve_safety_wit_27_normal_state : sx_solve_safety_wit_27_normal_state.
Axiom proof_of_sx_solve_safety_wit_28_normal_state : sx_solve_safety_wit_28_normal_state.
Axiom proof_of_sx_solve_safety_wit_29_normal_state : sx_solve_safety_wit_29_normal_state.
Axiom proof_of_sx_solve_safety_wit_30_normal_state : sx_solve_safety_wit_30_normal_state.
Axiom proof_of_sx_solve_safety_wit_31_normal_state : sx_solve_safety_wit_31_normal_state.
Axiom proof_of_sx_solve_safety_wit_32_normal_state : sx_solve_safety_wit_32_normal_state.
Axiom proof_of_sx_solve_safety_wit_33_normal_state : sx_solve_safety_wit_33_normal_state.
Axiom proof_of_sx_solve_safety_wit_34_normal_state : sx_solve_safety_wit_34_normal_state.
Axiom proof_of_sx_solve_safety_wit_35_normal_state : sx_solve_safety_wit_35_normal_state.
Axiom proof_of_sx_solve_safety_wit_36_normal_state : sx_solve_safety_wit_36_normal_state.
Axiom proof_of_sx_solve_safety_wit_37_normal_state : sx_solve_safety_wit_37_normal_state.
Axiom proof_of_sx_solve_entail_wit_1_normal_state : sx_solve_entail_wit_1_normal_state.
Axiom proof_of_sx_solve_entail_wit_2_normal_state : sx_solve_entail_wit_2_normal_state.
Axiom proof_of_sx_solve_entail_wit_3_normal_state : sx_solve_entail_wit_3_normal_state.
Axiom proof_of_sx_solve_entail_wit_4_normal_state : sx_solve_entail_wit_4_normal_state.
Axiom proof_of_sx_solve_entail_wit_5_1_normal_state : sx_solve_entail_wit_5_1_normal_state.
Axiom proof_of_sx_solve_entail_wit_5_2_normal_state : sx_solve_entail_wit_5_2_normal_state.
Axiom proof_of_sx_solve_entail_wit_6_1_normal_state : sx_solve_entail_wit_6_1_normal_state.
Axiom proof_of_sx_solve_entail_wit_6_2_normal_state : sx_solve_entail_wit_6_2_normal_state.
Axiom proof_of_sx_solve_entail_wit_7_1_normal_state : sx_solve_entail_wit_7_1_normal_state.
Axiom proof_of_sx_solve_entail_wit_7_2_normal_state : sx_solve_entail_wit_7_2_normal_state.
Axiom proof_of_sx_solve_entail_wit_8_normal_state : sx_solve_entail_wit_8_normal_state.
Axiom proof_of_sx_solve_return_wit_1_normal_state : sx_solve_return_wit_1_normal_state.
Axiom proof_of_sx_solve_return_wit_2_normal_state : sx_solve_return_wit_2_normal_state.
Axiom proof_of_sx_solve_return_wit_3_normal_state : sx_solve_return_wit_3_normal_state.
Axiom proof_of_sx_solve_return_wit_4_normal_state : sx_solve_return_wit_4_normal_state.
Axiom proof_of_sx_solve_return_wit_5_normal_state : sx_solve_return_wit_5_normal_state.
Axiom proof_of_sx_solve_return_wit_6_normal_state : sx_solve_return_wit_6_normal_state.
Axiom proof_of_sx_solve_return_wit_7_normal_state : sx_solve_return_wit_7_normal_state.
Axiom proof_of_sx_solve_return_wit_8_normal_state : sx_solve_return_wit_8_normal_state.
Axiom proof_of_sx_solve_return_wit_9_normal_state : sx_solve_return_wit_9_normal_state.
Axiom proof_of_sx_solve_return_wit_10_normal_state : sx_solve_return_wit_10_normal_state.
Axiom proof_of_sx_solve_return_wit_11_normal_state : sx_solve_return_wit_11_normal_state.
Axiom proof_of_sx_solve_return_wit_12_negative_budget : sx_solve_return_wit_12_negative_budget.
Axiom proof_of_sx_solve_partial_solve_wit_1_normal_state_pure : sx_solve_partial_solve_wit_1_normal_state_pure.
Axiom proof_of_sx_solve_partial_solve_wit_1_normal_state : sx_solve_partial_solve_wit_1_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_2_normal_state_pure : sx_solve_partial_solve_wit_2_normal_state_pure.
Axiom proof_of_sx_solve_partial_solve_wit_2_normal_state : sx_solve_partial_solve_wit_2_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_3_normal_state_pure : sx_solve_partial_solve_wit_3_normal_state_pure.
Axiom proof_of_sx_solve_partial_solve_wit_3_normal_state : sx_solve_partial_solve_wit_3_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_4_normal_state : sx_solve_partial_solve_wit_4_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_5_normal_state : sx_solve_partial_solve_wit_5_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_6_normal_state_pure : sx_solve_partial_solve_wit_6_normal_state_pure.
Axiom proof_of_sx_solve_partial_solve_wit_6_normal_state : sx_solve_partial_solve_wit_6_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_7_normal_state_pure : sx_solve_partial_solve_wit_7_normal_state_pure.
Axiom proof_of_sx_solve_partial_solve_wit_7_normal_state : sx_solve_partial_solve_wit_7_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_8_normal_state : sx_solve_partial_solve_wit_8_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_9_normal_state : sx_solve_partial_solve_wit_9_normal_state.
Axiom proof_of_sx_solve_partial_solve_wit_10_normal_state_pure : sx_solve_partial_solve_wit_10_normal_state_pure.
Axiom proof_of_sx_solve_partial_solve_wit_10_normal_state : sx_solve_partial_solve_wit_10_normal_state.

End VC_Correct.
