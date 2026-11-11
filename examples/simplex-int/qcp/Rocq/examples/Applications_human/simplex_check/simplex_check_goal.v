From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_initialize.simplex_initialize_lib.
Require Import SimpleC.EE.Applications_human.simplex_pivot.simplex_pivot_lib.
Require Import SimpleC.EE.Applications_human.simplex_solve.simplex_solve_lib.
Require Import SimpleC.EE.Applications_human.simplex_check.simplex_check_lib.
Local Open Scope sac.

(*----- Function sx_check -----*)

Definition sx_check_safety_wit_1_matrix_normal_budget :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_normal_budget)) (PreH4 : (c_pre = C_matrix_normal_budget)) (PreH5 : (inputs_pre = N_matrix_normal_budget)) (PreH6 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH7 : (rows_pre = M_matrix_normal_budget)) (PreH8 : (1 <= M_matrix_normal_budget)) (PreH9 : (M_matrix_normal_budget <= 16)) (PreH10 : (0 <= N_matrix_normal_budget)) (PreH11 : (N_matrix_normal_budget <= 8)) (PreH12 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH15 : (0 <= L_matrix_normal_budget)) (PreH16 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_2_matrix_negative_budget :=
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_3_zero_normal_budget :=
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_normal_budget)) (PreH4 : (c_pre = C_zero_normal_budget)) (PreH5 : (inputs_pre = N_zero_normal_budget)) (PreH6 : (pivot_limit_pre = L_zero_normal_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_normal_budget)) (PreH9 : (N_zero_normal_budget <= 8)) (PreH10 : (0 <= L_zero_normal_budget)) (PreH11 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_4_zero_negative_budget :=
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_5_check_rejected_coefficient :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_6_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_7_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_8_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_9_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition sx_check_safety_wit_10_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_11_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_12_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_13_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_14_check_rejected_coefficient :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_15_zero_negative_budget :=
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_16_zero_normal_budget :=
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_normal_budget)) (PreH4 : (c_pre = C_zero_normal_budget)) (PreH5 : (inputs_pre = N_zero_normal_budget)) (PreH6 : (pivot_limit_pre = L_zero_normal_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_normal_budget)) (PreH9 : (N_zero_normal_budget <= 8)) (PreH10 : (0 <= L_zero_normal_budget)) (PreH11 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_17_matrix_negative_budget :=
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_safety_wit_18_matrix_normal_budget :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_normal_budget)) (PreH4 : (c_pre = C_matrix_normal_budget)) (PreH5 : (inputs_pre = N_matrix_normal_budget)) (PreH6 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH7 : (rows_pre = M_matrix_normal_budget)) (PreH8 : (1 <= M_matrix_normal_budget)) (PreH9 : (M_matrix_normal_budget <= 16)) (PreH10 : (0 <= N_matrix_normal_budget)) (PreH11 : (N_matrix_normal_budget <= 8)) (PreH12 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH15 : (0 <= L_matrix_normal_budget)) (PreH16 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_return_wit_1_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_invalid_dimensions)) (PreH5 : (c_pre = C_check_invalid_dimensions)) (PreH6 : (rows_pre = M_check_invalid_dimensions)) (PreH7 : (inputs_pre = N_check_invalid_dimensions)) (PreH8 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH9 : (M_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ (retval = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_2_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_invalid_dimensions)) (PreH5 : (c_pre = C_check_invalid_dimensions)) (PreH6 : (rows_pre = M_check_invalid_dimensions)) (PreH7 : (inputs_pre = N_check_invalid_dimensions)) (PreH8 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH9 : (M_check_invalid_dimensions > 16)),
  TT && emp 
|--
  “ (retval = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_3_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_invalid_dimensions)) (PreH5 : (c_pre = C_check_invalid_dimensions)) (PreH6 : (rows_pre = M_check_invalid_dimensions)) (PreH7 : (inputs_pre = N_check_invalid_dimensions)) (PreH8 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH9 : (N_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ (retval = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_4_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_invalid_dimensions)) (PreH5 : (c_pre = C_check_invalid_dimensions)) (PreH6 : (rows_pre = M_check_invalid_dimensions)) (PreH7 : (inputs_pre = N_check_invalid_dimensions)) (PreH8 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH9 : (N_check_invalid_dimensions > 8)),
  TT && emp 
|--
  “ (retval = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_5_check_rejected_coefficient :=
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_rejected_coefficient)) (PreH5 : (c_pre = C_check_rejected_coefficient)) (PreH6 : (rows_pre = M_check_rejected_coefficient)) (PreH7 : (inputs_pre = N_check_rejected_coefficient)) (PreH8 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH9 : (0 <= M_check_rejected_coefficient)) (PreH10 : (M_check_rejected_coefficient <= 16)) (PreH11 : (0 <= N_check_rejected_coefficient)) (PreH12 : (N_check_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH16 : (0 <= x)) (PreH17 : (x < M_check_rejected_coefficient)) (PreH18 : (0 <= y)) (PreH19 : (y <= N_check_rejected_coefficient)) (PreH20 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
|--
  “ (retval = (-1)) ”
  &&  “ (simplex_check_rejected_result A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient L_check_rejected_coefficient retval ) ”
  &&  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
) \/
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_rejected_coefficient)) (PreH5 : (c_pre = C_check_rejected_coefficient)) (PreH6 : (rows_pre = M_check_rejected_coefficient)) (PreH7 : (inputs_pre = N_check_rejected_coefficient)) (PreH8 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH9 : (0 <= M_check_rejected_coefficient)) (PreH10 : (M_check_rejected_coefficient <= 16)) (PreH11 : (0 <= N_check_rejected_coefficient)) (PreH12 : (N_check_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH16 : (0 <= x)) (PreH17 : (x < M_check_rejected_coefficient)) (PreH18 : (0 <= y)) (PreH19 : (y <= N_check_rejected_coefficient)) (PreH20 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  TT && emp 
|--
  “ (simplex_check_rejected_result A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient L_check_rejected_coefficient (-1) ) ”
  &&  emp
).

Definition sx_check_return_wit_5_check_rejected_coefficient_split_goal_1 :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 0 )) (PreH4 : (s_pre = S_check_rejected_coefficient)) (PreH5 : (c_pre = C_check_rejected_coefficient)) (PreH6 : (rows_pre = M_check_rejected_coefficient)) (PreH7 : (inputs_pre = N_check_rejected_coefficient)) (PreH8 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH9 : (0 <= M_check_rejected_coefficient)) (PreH10 : (M_check_rejected_coefficient <= 16)) (PreH11 : (0 <= N_check_rejected_coefficient)) (PreH12 : (N_check_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH16 : (0 <= x)) (PreH17 : (x < M_check_rejected_coefficient)) (PreH18 : (0 <= y)) (PreH19 : (y <= N_check_rejected_coefficient)) (PreH20 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_check_rejected_result A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient L_check_rejected_coefficient (-1) )
.

Definition sx_check_return_wit_6_zero_negative_budget :=
(
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 1 )) (PreH4 : (s_pre = S_zero_negative_budget)) (PreH5 : (c_pre = C_zero_negative_budget)) (PreH6 : (inputs_pre = N_zero_negative_budget)) (PreH7 : (pivot_limit_pre = L_zero_negative_budget)) (PreH8 : (rows_pre = 0)) (PreH9 : (0 <= N_zero_negative_budget)) (PreH10 : (N_zero_negative_budget <= 8)) (PreH11 : ((INT_MIN) <= L_zero_negative_budget)) (PreH12 : (L_zero_negative_budget < 0)),
  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
|--
  “ (retval = (-1)) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_negative_budget L_zero_negative_budget retval (simplex_check_initial_num ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_zero_negative_budget) (0)) (simplex_init_flags (N_zero_negative_budget) ((0 + N_zero_negative_budget ))) (simplex_init_values ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones ((0 + N_zero_negative_budget ))) ) ”
  &&  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
) \/
(
forall (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 1 )) (PreH4 : (s_pre = S_zero_negative_budget)) (PreH5 : (c_pre = C_zero_negative_budget)) (PreH6 : (inputs_pre = N_zero_negative_budget)) (PreH7 : (pivot_limit_pre = L_zero_negative_budget)) (PreH8 : (rows_pre = 0)) (PreH9 : (0 <= N_zero_negative_budget)) (PreH10 : (N_zero_negative_budget <= 8)) (PreH11 : ((INT_MIN) <= L_zero_negative_budget)) (PreH12 : (L_zero_negative_budget < 0)),
  TT && emp 
|--
  “ (simplex_check_result (@nil Z) 0 N_zero_negative_budget L_zero_negative_budget (-1) (simplex_check_initial_num ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_zero_negative_budget) (0)) (simplex_init_flags (N_zero_negative_budget) ((0 + N_zero_negative_budget ))) (simplex_init_values ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones ((0 + N_zero_negative_budget ))) ) ”
  &&  emp
).

Definition sx_check_return_wit_6_zero_negative_budget_split_goal_1 :=
forall (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 1 )) (PreH4 : (s_pre = S_zero_negative_budget)) (PreH5 : (c_pre = C_zero_negative_budget)) (PreH6 : (inputs_pre = N_zero_negative_budget)) (PreH7 : (pivot_limit_pre = L_zero_negative_budget)) (PreH8 : (rows_pre = 0)) (PreH9 : (0 <= N_zero_negative_budget)) (PreH10 : (N_zero_negative_budget <= 8)) (PreH11 : ((INT_MIN) <= L_zero_negative_budget)) (PreH12 : (L_zero_negative_budget < 0)),
  (simplex_check_result (@nil Z) 0 N_zero_negative_budget L_zero_negative_budget (-1) (simplex_check_initial_num ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_zero_negative_budget) (0)) (simplex_init_flags (N_zero_negative_budget) ((0 + N_zero_negative_budget ))) (simplex_init_values ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones ((0 + N_zero_negative_budget ))) )
.

Definition sx_check_return_wit_7_zero_normal_budget :=
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB_2 )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB_2 )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON_2 OD_2 )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN_2 OVD_2 (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_init_return retval 0 ) ”
  &&  “ (retval = 1) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON OD )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN OVD (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
) \/
(
forall (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  TT && emp 
|--
  “ (simplex_init_return 1 0 ) ”
  &&  emp
).

Definition sx_check_return_wit_7_zero_normal_budget_split_goal_1 :=
forall (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  (simplex_init_return 1 0 )
.

Definition sx_check_return_wit_8_zero_normal_budget :=
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB_2 )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB_2 )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON_2 OD_2 )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN_2 OVD_2 (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_init_return retval 0 ) ”
  &&  “ (retval = 0) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON OD )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN OVD (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
) \/
(
forall (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_check_return_wit_8_zero_normal_budget_split_goal_1 :=
forall (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  (simplex_init_return 0 0 )
.

Definition sx_check_return_wit_9_zero_normal_budget :=
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB_2 )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB_2 )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON_2 OD_2 )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN_2 OVD_2 (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_init_return retval 0 ) ”
  &&  “ (retval = (-1)) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON OD )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN OVD (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
) \/
(
forall (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  TT && emp 
|--
  “ (simplex_init_return (-1) 0 ) ”
  &&  emp
).

Definition sx_check_return_wit_9_zero_normal_budget_split_goal_1 :=
forall (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_zero_normal_budget)) (PreH9 : (c_pre = C_zero_normal_budget)) (PreH10 : (inputs_pre = N_zero_normal_budget)) (PreH11 : (pivot_limit_pre = L_zero_normal_budget)) (PreH12 : (rows_pre = 0)) (PreH13 : (0 <= N_zero_normal_budget)) (PreH14 : (N_zero_normal_budget <= 8)) (PreH15 : (0 <= L_zero_normal_budget)) (PreH16 : (L_zero_normal_budget <= INT_MAX)),
  (simplex_init_return (-1) 0 )
.

Definition sx_check_return_wit_10_matrix_negative_budget :=
(
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 1 )) (PreH4 : (s_pre = S_matrix_negative_budget)) (PreH5 : (c_pre = C_matrix_negative_budget)) (PreH6 : (inputs_pre = N_matrix_negative_budget)) (PreH7 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH8 : (rows_pre = M_matrix_negative_budget)) (PreH9 : (1 <= M_matrix_negative_budget)) (PreH10 : (M_matrix_negative_budget <= 16)) (PreH11 : (0 <= N_matrix_negative_budget)) (PreH12 : (N_matrix_negative_budget <= 8)) (PreH13 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH16 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH17 : (L_matrix_negative_budget < 0)),
  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
|--
  “ (retval = (-1)) ”
  &&  “ (simplex_check_result A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget retval (simplex_check_initial_num (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_matrix_negative_budget) (M_matrix_negative_budget)) (simplex_init_flags (N_matrix_negative_budget) ((M_matrix_negative_budget + N_matrix_negative_budget ))) (simplex_init_values (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones ((M_matrix_negative_budget + N_matrix_negative_budget ))) ) ”
  &&  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
) \/
(
forall (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 1 )) (PreH4 : (s_pre = S_matrix_negative_budget)) (PreH5 : (c_pre = C_matrix_negative_budget)) (PreH6 : (inputs_pre = N_matrix_negative_budget)) (PreH7 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH8 : (rows_pre = M_matrix_negative_budget)) (PreH9 : (1 <= M_matrix_negative_budget)) (PreH10 : (M_matrix_negative_budget <= 16)) (PreH11 : (0 <= N_matrix_negative_budget)) (PreH12 : (N_matrix_negative_budget <= 8)) (PreH13 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH16 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH17 : (L_matrix_negative_budget < 0)),
  TT && emp 
|--
  “ (simplex_check_result A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget (-1) (simplex_check_initial_num (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_matrix_negative_budget) (M_matrix_negative_budget)) (simplex_init_flags (N_matrix_negative_budget) ((M_matrix_negative_budget + N_matrix_negative_budget ))) (simplex_init_values (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones ((M_matrix_negative_budget + N_matrix_negative_budget ))) ) ”
  &&  emp
).

Definition sx_check_return_wit_10_matrix_negative_budget_split_goal_1 :=
forall (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (retval_2 <> 0)) (PreH3 : (simplex_init_return retval_2 1 )) (PreH4 : (s_pre = S_matrix_negative_budget)) (PreH5 : (c_pre = C_matrix_negative_budget)) (PreH6 : (inputs_pre = N_matrix_negative_budget)) (PreH7 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH8 : (rows_pre = M_matrix_negative_budget)) (PreH9 : (1 <= M_matrix_negative_budget)) (PreH10 : (M_matrix_negative_budget <= 16)) (PreH11 : (0 <= N_matrix_negative_budget)) (PreH12 : (N_matrix_negative_budget <= 8)) (PreH13 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH16 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH17 : (L_matrix_negative_budget < 0)),
  (simplex_check_result A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget (-1) (simplex_check_initial_num (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_matrix_negative_budget) (M_matrix_negative_budget)) (simplex_init_flags (N_matrix_negative_budget) ((M_matrix_negative_budget + N_matrix_negative_budget ))) (simplex_init_values (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones ((M_matrix_negative_budget + N_matrix_negative_budget ))) )
.

Definition sx_check_return_wit_11_matrix_normal_budget :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_matrix_normal_budget)) (PreH9 : (c_pre = C_matrix_normal_budget)) (PreH10 : (inputs_pre = N_matrix_normal_budget)) (PreH11 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH12 : (rows_pre = M_matrix_normal_budget)) (PreH13 : (1 <= M_matrix_normal_budget)) (PreH14 : (M_matrix_normal_budget <= 16)) (PreH15 : (0 <= N_matrix_normal_budget)) (PreH16 : (N_matrix_normal_budget <= 8)) (PreH17 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH18 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH19 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH20 : (0 <= L_matrix_normal_budget)) (PreH21 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB_2 )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB_2 )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON_2 OD_2 )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN_2 OVD_2 (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 1) ”
  &&  “ (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON OD )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN OVD (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
.

Definition sx_check_return_wit_12_matrix_normal_budget :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_matrix_normal_budget)) (PreH9 : (c_pre = C_matrix_normal_budget)) (PreH10 : (inputs_pre = N_matrix_normal_budget)) (PreH11 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH12 : (rows_pre = M_matrix_normal_budget)) (PreH13 : (1 <= M_matrix_normal_budget)) (PreH14 : (M_matrix_normal_budget <= 16)) (PreH15 : (0 <= N_matrix_normal_budget)) (PreH16 : (N_matrix_normal_budget <= 8)) (PreH17 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH18 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH19 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH20 : (0 <= L_matrix_normal_budget)) (PreH21 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB_2 )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB_2 )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON_2 OD_2 )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN_2 OVD_2 (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 0) ”
  &&  “ (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON OD )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN OVD (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
.

Definition sx_check_return_wit_13_matrix_normal_budget :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval_2: Z) (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)) (retval: Z) (PreH1 : (retval = (-1))) (PreH2 : (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 )) (PreH3 : ((retval = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN_2 OVD_2 ))) (PreH4 : ((retval = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget ))) (PreH5 : ((retval <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) )))) (PreH6 : (retval_2 <> 0)) (PreH7 : (simplex_init_return retval_2 1 )) (PreH8 : (s_pre = S_matrix_normal_budget)) (PreH9 : (c_pre = C_matrix_normal_budget)) (PreH10 : (inputs_pre = N_matrix_normal_budget)) (PreH11 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH12 : (rows_pre = M_matrix_normal_budget)) (PreH13 : (1 <= M_matrix_normal_budget)) (PreH14 : (M_matrix_normal_budget <= 16)) (PreH15 : (0 <= N_matrix_normal_budget)) (PreH16 : (N_matrix_normal_budget <= 8)) (PreH17 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH18 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH19 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH20 : (0 <= L_matrix_normal_budget)) (PreH21 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB_2 )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB_2 )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON_2 OD_2 )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN_2 OVD_2 (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = (-1)) ”
  &&  “ (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON OD )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN OVD (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
.

Definition sx_check_return_wit_14_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ ((-1) = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_15_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions > 16)),
  TT && emp 
|--
  “ ((-1) = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_16_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ ((-1) = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_17_check_invalid_dimensions :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions > 8)),
  TT && emp 
|--
  “ ((-1) = (-1)) ”
  &&  emp
.

Definition sx_check_return_wit_18_check_rejected_coefficient :=
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
|--
  “ ((-1) = (-1)) ”
  &&  “ (simplex_check_rejected_result A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient L_check_rejected_coefficient (-1) ) ”
  &&  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
) \/
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  TT && emp 
|--
  “ (simplex_check_rejected_result A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient L_check_rejected_coefficient (-1) ) ”
  &&  emp
).

Definition sx_check_return_wit_18_check_rejected_coefficient_split_goal_1 :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_check_rejected_result A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient L_check_rejected_coefficient (-1) )
.

Definition sx_check_return_wit_19_zero_negative_budget :=
(
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
|--
  “ ((-1) = (-1)) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_negative_budget L_zero_negative_budget (-1) (simplex_check_initial_num ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_zero_negative_budget) (0)) (simplex_init_flags (N_zero_negative_budget) ((0 + N_zero_negative_budget ))) (simplex_init_values ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones ((0 + N_zero_negative_budget ))) ) ”
  &&  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
) \/
(
forall (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  TT && emp 
|--
  “ (simplex_check_result (@nil Z) 0 N_zero_negative_budget L_zero_negative_budget (-1) (simplex_check_initial_num ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_zero_negative_budget) (0)) (simplex_init_flags (N_zero_negative_budget) ((0 + N_zero_negative_budget ))) (simplex_init_values ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones ((0 + N_zero_negative_budget ))) ) ”
  &&  emp
).

Definition sx_check_return_wit_19_zero_negative_budget_split_goal_1 :=
forall (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  (simplex_check_result (@nil Z) 0 N_zero_negative_budget L_zero_negative_budget (-1) (simplex_check_initial_num ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_zero_negative_budget) (0)) (simplex_init_flags (N_zero_negative_budget) ((0 + N_zero_negative_budget ))) (simplex_init_values ((@nil Z)) (0) (N_zero_negative_budget)) (simplex_init_ones ((0 + N_zero_negative_budget ))) )
.

Definition sx_check_return_wit_20_zero_normal_budget :=
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_normal_budget)) (PreH4 : (c_pre = C_zero_normal_budget)) (PreH5 : (inputs_pre = N_zero_normal_budget)) (PreH6 : (pivot_limit_pre = L_zero_normal_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_normal_budget)) (PreH9 : (N_zero_normal_budget <= 8)) (PreH10 : (0 <= L_zero_normal_budget)) (PreH11 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_init_return (-1) 0 ) ”
  &&  “ ((-1) = (-1)) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget )) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "basic") 0 OB )
  **  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON OD )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN OVD (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
) \/
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_normal_budget)) (PreH4 : (c_pre = C_zero_normal_budget)) (PreH5 : (inputs_pre = N_zero_normal_budget)) (PreH6 : (pivot_limit_pre = L_zero_normal_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_normal_budget)) (PreH9 : (N_zero_normal_budget <= 8)) (PreH10 : (0 <= L_zero_normal_budget)) (PreH11 : (L_zero_normal_budget <= INT_MAX)),
  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_init_return (-1) 0 ) ”
  &&  “ (simplex_check_result (@nil Z) 0 N_zero_normal_budget L_zero_normal_budget (-1) ON OD (@nil Z) OIB OVN OVD ) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness (@nil Z) 0 N_zero_normal_budget OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat (@nil Z) 0 N_zero_normal_budget )) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) ((@nil Z)) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin (@nil Z) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) 0 N_zero_normal_budget (simplex_solve_pack (ON) (OD) ((@nil Z)) (OIB) (OVN) (OVD)) ))) ”
  &&  (IntArray.full &((S_zero_normal_budget)  # "SxState" ->ₛ "is_basic") (0 + N_zero_normal_budget ) OIB )
  **  (simplex_pivot_memory S_zero_normal_budget 0 (0 + N_zero_normal_budget ) ON OD )
  **  (simplex_solve_variables S_zero_normal_budget (0 + N_zero_normal_budget ) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_flags (N_zero_normal_budget) ((0 + N_zero_normal_budget ))) OVN OVD (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) (simplex_init_zeroes ((0 + N_zero_normal_budget ))) (simplex_init_ones ((0 + N_zero_normal_budget ))) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
).

Definition sx_check_return_wit_21_matrix_negative_budget :=
(
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
|--
  “ ((-1) = (-1)) ”
  &&  “ (simplex_check_result A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget (-1) (simplex_check_initial_num (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_matrix_negative_budget) (M_matrix_negative_budget)) (simplex_init_flags (N_matrix_negative_budget) ((M_matrix_negative_budget + N_matrix_negative_budget ))) (simplex_init_values (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones ((M_matrix_negative_budget + N_matrix_negative_budget ))) ) ”
  &&  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
) \/
(
forall (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  TT && emp 
|--
  “ (simplex_check_result A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget (-1) (simplex_check_initial_num (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_matrix_negative_budget) (M_matrix_negative_budget)) (simplex_init_flags (N_matrix_negative_budget) ((M_matrix_negative_budget + N_matrix_negative_budget ))) (simplex_init_values (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones ((M_matrix_negative_budget + N_matrix_negative_budget ))) ) ”
  &&  emp
).

Definition sx_check_return_wit_21_matrix_negative_budget_split_goal_1 :=
forall (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  (simplex_check_result A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget L_matrix_negative_budget (-1) (simplex_check_initial_num (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones (400)) (simplex_init_basic (N_matrix_negative_budget) (M_matrix_negative_budget)) (simplex_init_flags (N_matrix_negative_budget) ((M_matrix_negative_budget + N_matrix_negative_budget ))) (simplex_init_values (A_matrix_negative_budget) (M_matrix_negative_budget) (N_matrix_negative_budget)) (simplex_init_ones ((M_matrix_negative_budget + N_matrix_negative_budget ))) )
.

Definition sx_check_return_wit_22_matrix_normal_budget :=
(
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_normal_budget)) (PreH4 : (c_pre = C_matrix_normal_budget)) (PreH5 : (inputs_pre = N_matrix_normal_budget)) (PreH6 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH7 : (rows_pre = M_matrix_normal_budget)) (PreH8 : (1 <= M_matrix_normal_budget)) (PreH9 : (M_matrix_normal_budget <= 16)) (PreH10 : (0 <= N_matrix_normal_budget)) (PreH11 : (N_matrix_normal_budget <= 8)) (PreH12 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH15 : (0 <= L_matrix_normal_budget)) (PreH16 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ ((-1) = (-1)) ”
  &&  “ (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON OD )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN OVD (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
) \/
(
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_normal_budget)) (PreH4 : (c_pre = C_matrix_normal_budget)) (PreH5 : (inputs_pre = N_matrix_normal_budget)) (PreH6 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH7 : (rows_pre = M_matrix_normal_budget)) (PreH8 : (1 <= M_matrix_normal_budget)) (PreH9 : (M_matrix_normal_budget <= 16)) (PreH10 : (0 <= N_matrix_normal_budget)) (PreH11 : (N_matrix_normal_budget <= 8)) (PreH12 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH15 : (0 <= L_matrix_normal_budget)) (PreH16 : (L_matrix_normal_budget <= INT_MAX)),
  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (simplex_check_result A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget L_matrix_normal_budget (-1) ON OD OB OIB OVN OVD ) ”
  &&  “ (((-1) = 0) -> (simplex_solve_witness A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget OVN OVD )) ”
  &&  “ (((-1) = 1) -> (simplex_solve_unsat A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )) ”
  &&  “ (((-1) <> (-1)) -> ((simplex_solve_normal A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_matrix_normal_budget (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) M_matrix_normal_budget N_matrix_normal_budget (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "basic") M_matrix_normal_budget OB )
  **  (IntArray.full &((S_matrix_normal_budget)  # "SxState" ->ₛ "is_basic") (M_matrix_normal_budget + N_matrix_normal_budget ) OIB )
  **  (simplex_pivot_memory S_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) ON OD )
  **  (simplex_solve_variables S_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_flags (N_matrix_normal_budget) ((M_matrix_normal_budget + N_matrix_normal_budget ))) OVN OVD (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_zeroes ((M_matrix_normal_budget + N_matrix_normal_budget ))) (simplex_init_ones ((M_matrix_normal_budget + N_matrix_normal_budget ))) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
).

Definition sx_check_partial_solve_wit_1_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
).

Definition sx_check_partial_solve_wit_1_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
.

Definition sx_check_partial_solve_wit_1_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (M_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (M_check_invalid_dimensions < 0) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_1_check_invalid_dimensions := sx_check_partial_solve_wit_1_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_1_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_2_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
).

Definition sx_check_partial_solve_wit_2_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
.

Definition sx_check_partial_solve_wit_2_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (M_check_invalid_dimensions > 16)),
  TT && emp 
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (M_check_invalid_dimensions > 16) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_2_check_invalid_dimensions := sx_check_partial_solve_wit_2_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_2_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_3_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
).

Definition sx_check_partial_solve_wit_3_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
.

Definition sx_check_partial_solve_wit_3_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (N_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (N_check_invalid_dimensions < 0) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_3_check_invalid_dimensions := sx_check_partial_solve_wit_3_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_3_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_4_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
).

Definition sx_check_partial_solve_wit_4_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_invalid_dimensions)) (PreH8 : (c_pre = C_check_invalid_dimensions)) (PreH9 : (rows_pre = M_check_invalid_dimensions)) (PreH10 : (inputs_pre = N_check_invalid_dimensions)) (PreH11 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH12 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
.

Definition sx_check_partial_solve_wit_4_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_invalid_dimensions)) (PreH2 : (c_pre = C_check_invalid_dimensions)) (PreH3 : (rows_pre = M_check_invalid_dimensions)) (PreH4 : (inputs_pre = N_check_invalid_dimensions)) (PreH5 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH6 : (N_check_invalid_dimensions > 8)),
  TT && emp 
|--
  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (simplex_check_invalid_dimensions M_check_invalid_dimensions N_check_invalid_dimensions ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (N_check_invalid_dimensions > 8) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_4_check_invalid_dimensions := sx_check_partial_solve_wit_4_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_4_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_5_check_rejected_coefficient_pure :=
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x_2: Z) (y_2: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_rejected_coefficient)) (PreH2 : (c_pre = C_check_rejected_coefficient)) (PreH3 : (rows_pre = M_check_rejected_coefficient)) (PreH4 : (inputs_pre = N_check_rejected_coefficient)) (PreH5 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH6 : (0 <= M_check_rejected_coefficient)) (PreH7 : (M_check_rejected_coefficient <= 16)) (PreH8 : (0 <= N_check_rejected_coefficient)) (PreH9 : (N_check_rejected_coefficient <= 8)) (PreH10 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH11 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH13 : (0 <= x_2)) (PreH14 : (x_2 < M_check_rejected_coefficient)) (PreH15 : (0 <= y_2)) (PreH16 : (y_2 <= N_check_rejected_coefficient)) (PreH17 : ((Znth (((x_2 * 9 ) + y_2 )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (s_pre = S_check_rejected_coefficient) ”
  &&  “ (rows_pre = M_check_rejected_coefficient) ”
  &&  “ (inputs_pre = N_check_rejected_coefficient) ”
  &&  “ (c_pre = C_check_rejected_coefficient) ”
  &&  “ (0 <= M_check_rejected_coefficient) ”
  &&  “ (M_check_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_check_rejected_coefficient) ”
  &&  “ (N_check_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient ) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (y <= N_check_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (x < M_check_rejected_coefficient) ”
  &&  “ (0 <= x) ”
) \/
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x_2: Z) (y_2: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (s_pre = S_check_rejected_coefficient)) (PreH8 : (c_pre = C_check_rejected_coefficient)) (PreH9 : (rows_pre = M_check_rejected_coefficient)) (PreH10 : (inputs_pre = N_check_rejected_coefficient)) (PreH11 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH12 : (0 <= M_check_rejected_coefficient)) (PreH13 : (M_check_rejected_coefficient <= 16)) (PreH14 : (0 <= N_check_rejected_coefficient)) (PreH15 : (N_check_rejected_coefficient <= 8)) (PreH16 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH17 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH18 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH19 : (0 <= x_2)) (PreH20 : (x_2 < M_check_rejected_coefficient)) (PreH21 : (0 <= y_2)) (PreH22 : (y_2 <= N_check_rejected_coefficient)) (PreH23 : ((Znth (((x_2 * 9 ) + y_2 )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (y <= N_check_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (x < M_check_rejected_coefficient) ”
  &&  “ (0 <= x) ”
).

Definition sx_check_partial_solve_wit_5_check_rejected_coefficient_aux :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x_2: Z) (y_2: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_check_rejected_coefficient)) (PreH2 : (c_pre = C_check_rejected_coefficient)) (PreH3 : (rows_pre = M_check_rejected_coefficient)) (PreH4 : (inputs_pre = N_check_rejected_coefficient)) (PreH5 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH6 : (0 <= M_check_rejected_coefficient)) (PreH7 : (M_check_rejected_coefficient <= 16)) (PreH8 : (0 <= N_check_rejected_coefficient)) (PreH9 : (N_check_rejected_coefficient <= 8)) (PreH10 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH11 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH13 : (0 <= x_2)) (PreH14 : (x_2 < M_check_rejected_coefficient)) (PreH15 : (0 <= y_2)) (PreH16 : (y_2 <= N_check_rejected_coefficient)) (PreH17 : ((Znth (((x_2 * 9 ) + y_2 )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (s_pre = S_check_rejected_coefficient) ”
  &&  “ (rows_pre = M_check_rejected_coefficient) ”
  &&  “ (inputs_pre = N_check_rejected_coefficient) ”
  &&  “ (c_pre = C_check_rejected_coefficient) ”
  &&  “ (0 <= M_check_rejected_coefficient) ”
  &&  “ (M_check_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_check_rejected_coefficient) ”
  &&  “ (N_check_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient ) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (y <= N_check_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (x < M_check_rejected_coefficient) ”
  &&  “ (0 <= x) ”
  &&  “ (s_pre = S_check_rejected_coefficient) ”
  &&  “ (c_pre = C_check_rejected_coefficient) ”
  &&  “ (rows_pre = M_check_rejected_coefficient) ”
  &&  “ (inputs_pre = N_check_rejected_coefficient) ”
  &&  “ (pivot_limit_pre = L_check_rejected_coefficient) ”
  &&  “ (0 <= M_check_rejected_coefficient) ”
  &&  “ (M_check_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_check_rejected_coefficient) ”
  &&  “ (N_check_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient ) ”
  &&  “ (0 <= x_2) ”
  &&  “ (x_2 < M_check_rejected_coefficient) ”
  &&  “ (0 <= y_2) ”
  &&  “ (y_2 <= N_check_rejected_coefficient) ”
  &&  “ ((Znth (((x_2 * 9 ) + y_2 )) (A_check_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
.

Definition sx_check_partial_solve_wit_5_check_rejected_coefficient := sx_check_partial_solve_wit_5_check_rejected_coefficient_pure -> sx_check_partial_solve_wit_5_check_rejected_coefficient_aux.

Definition sx_check_partial_solve_wit_6_zero_negative_budget_pure :=
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_zero_negative_budget)) (PreH2 : (c_pre = C_zero_negative_budget)) (PreH3 : (inputs_pre = N_zero_negative_budget)) (PreH4 : (pivot_limit_pre = L_zero_negative_budget)) (PreH5 : (rows_pre = 0)) (PreH6 : (0 <= N_zero_negative_budget)) (PreH7 : (N_zero_negative_budget <= 8)) (PreH8 : ((INT_MIN) <= L_zero_negative_budget)) (PreH9 : (L_zero_negative_budget < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  (simplex_check_old S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
|--
  “ (s_pre = S_zero_negative_budget) ”
  &&  “ (c_pre = C_zero_negative_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N_zero_negative_budget) ”
  &&  “ (0 <= N_zero_negative_budget) ”
  &&  “ (N_zero_negative_budget <= 8) ”
.

Definition sx_check_partial_solve_wit_6_zero_negative_budget_aux :=
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_zero_negative_budget)) (PreH2 : (c_pre = C_zero_negative_budget)) (PreH3 : (inputs_pre = N_zero_negative_budget)) (PreH4 : (pivot_limit_pre = L_zero_negative_budget)) (PreH5 : (rows_pre = 0)) (PreH6 : (0 <= N_zero_negative_budget)) (PreH7 : (N_zero_negative_budget <= 8)) (PreH8 : ((INT_MIN) <= L_zero_negative_budget)) (PreH9 : (L_zero_negative_budget < 0)),
  (simplex_check_old S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
|--
  “ (s_pre = S_zero_negative_budget) ”
  &&  “ (c_pre = C_zero_negative_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N_zero_negative_budget) ”
  &&  “ (0 <= N_zero_negative_budget) ”
  &&  “ (N_zero_negative_budget <= 8) ”
  &&  “ (s_pre = S_zero_negative_budget) ”
  &&  “ (c_pre = C_zero_negative_budget) ”
  &&  “ (inputs_pre = N_zero_negative_budget) ”
  &&  “ (pivot_limit_pre = L_zero_negative_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (0 <= N_zero_negative_budget) ”
  &&  “ (N_zero_negative_budget <= 8) ”
  &&  “ ((INT_MIN) <= L_zero_negative_budget) ”
  &&  “ (L_zero_negative_budget < 0) ”
  &&  (simplex_check_old S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
.

Definition sx_check_partial_solve_wit_6_zero_negative_budget := sx_check_partial_solve_wit_6_zero_negative_budget_pure -> sx_check_partial_solve_wit_6_zero_negative_budget_aux.

Definition sx_check_partial_solve_wit_7_zero_normal_budget_pure :=
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_zero_normal_budget)) (PreH2 : (c_pre = C_zero_normal_budget)) (PreH3 : (inputs_pre = N_zero_normal_budget)) (PreH4 : (pivot_limit_pre = L_zero_normal_budget)) (PreH5 : (rows_pre = 0)) (PreH6 : (0 <= N_zero_normal_budget)) (PreH7 : (N_zero_normal_budget <= 8)) (PreH8 : (0 <= L_zero_normal_budget)) (PreH9 : (L_zero_normal_budget <= INT_MAX)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  (simplex_check_old S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  “ (s_pre = S_zero_normal_budget) ”
  &&  “ (c_pre = C_zero_normal_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N_zero_normal_budget) ”
  &&  “ (0 <= N_zero_normal_budget) ”
  &&  “ (N_zero_normal_budget <= 8) ”
.

Definition sx_check_partial_solve_wit_7_zero_normal_budget_aux :=
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_zero_normal_budget)) (PreH2 : (c_pre = C_zero_normal_budget)) (PreH3 : (inputs_pre = N_zero_normal_budget)) (PreH4 : (pivot_limit_pre = L_zero_normal_budget)) (PreH5 : (rows_pre = 0)) (PreH6 : (0 <= N_zero_normal_budget)) (PreH7 : (N_zero_normal_budget <= 8)) (PreH8 : (0 <= L_zero_normal_budget)) (PreH9 : (L_zero_normal_budget <= INT_MAX)),
  (simplex_check_old S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  “ (s_pre = S_zero_normal_budget) ”
  &&  “ (c_pre = C_zero_normal_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N_zero_normal_budget) ”
  &&  “ (0 <= N_zero_normal_budget) ”
  &&  “ (N_zero_normal_budget <= 8) ”
  &&  “ (s_pre = S_zero_normal_budget) ”
  &&  “ (c_pre = C_zero_normal_budget) ”
  &&  “ (inputs_pre = N_zero_normal_budget) ”
  &&  “ (pivot_limit_pre = L_zero_normal_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (0 <= N_zero_normal_budget) ”
  &&  “ (N_zero_normal_budget <= 8) ”
  &&  “ (0 <= L_zero_normal_budget) ”
  &&  “ (L_zero_normal_budget <= INT_MAX) ”
  &&  (simplex_check_old S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
.

Definition sx_check_partial_solve_wit_7_zero_normal_budget := sx_check_partial_solve_wit_7_zero_normal_budget_pure -> sx_check_partial_solve_wit_7_zero_normal_budget_aux.

Definition sx_check_partial_solve_wit_8_matrix_negative_budget_pure :=
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_matrix_negative_budget)) (PreH2 : (c_pre = C_matrix_negative_budget)) (PreH3 : (inputs_pre = N_matrix_negative_budget)) (PreH4 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH5 : (rows_pre = M_matrix_negative_budget)) (PreH6 : (1 <= M_matrix_negative_budget)) (PreH7 : (M_matrix_negative_budget <= 16)) (PreH8 : (0 <= N_matrix_negative_budget)) (PreH9 : (N_matrix_negative_budget <= 8)) (PreH10 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH13 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH14 : (L_matrix_negative_budget < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  (simplex_check_old S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
|--
  “ (s_pre = S_matrix_negative_budget) ”
  &&  “ (c_pre = C_matrix_negative_budget) ”
  &&  “ (rows_pre = M_matrix_negative_budget) ”
  &&  “ (inputs_pre = N_matrix_negative_budget) ”
  &&  “ (1 <= M_matrix_negative_budget) ”
  &&  “ (M_matrix_negative_budget <= 16) ”
  &&  “ (0 <= N_matrix_negative_budget) ”
  &&  “ (N_matrix_negative_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget ) ”
.

Definition sx_check_partial_solve_wit_8_matrix_negative_budget_aux :=
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_matrix_negative_budget)) (PreH2 : (c_pre = C_matrix_negative_budget)) (PreH3 : (inputs_pre = N_matrix_negative_budget)) (PreH4 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH5 : (rows_pre = M_matrix_negative_budget)) (PreH6 : (1 <= M_matrix_negative_budget)) (PreH7 : (M_matrix_negative_budget <= 16)) (PreH8 : (0 <= N_matrix_negative_budget)) (PreH9 : (N_matrix_negative_budget <= 8)) (PreH10 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH13 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH14 : (L_matrix_negative_budget < 0)),
  (simplex_check_old S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
|--
  “ (s_pre = S_matrix_negative_budget) ”
  &&  “ (c_pre = C_matrix_negative_budget) ”
  &&  “ (rows_pre = M_matrix_negative_budget) ”
  &&  “ (inputs_pre = N_matrix_negative_budget) ”
  &&  “ (1 <= M_matrix_negative_budget) ”
  &&  “ (M_matrix_negative_budget <= 16) ”
  &&  “ (0 <= N_matrix_negative_budget) ”
  &&  “ (N_matrix_negative_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget ) ”
  &&  “ (s_pre = S_matrix_negative_budget) ”
  &&  “ (c_pre = C_matrix_negative_budget) ”
  &&  “ (inputs_pre = N_matrix_negative_budget) ”
  &&  “ (pivot_limit_pre = L_matrix_negative_budget) ”
  &&  “ (rows_pre = M_matrix_negative_budget) ”
  &&  “ (1 <= M_matrix_negative_budget) ”
  &&  “ (M_matrix_negative_budget <= 16) ”
  &&  “ (0 <= N_matrix_negative_budget) ”
  &&  “ (N_matrix_negative_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget ) ”
  &&  “ ((INT_MIN) <= L_matrix_negative_budget) ”
  &&  “ (L_matrix_negative_budget < 0) ”
  &&  (simplex_check_old S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
.

Definition sx_check_partial_solve_wit_8_matrix_negative_budget := sx_check_partial_solve_wit_8_matrix_negative_budget_pure -> sx_check_partial_solve_wit_8_matrix_negative_budget_aux.

Definition sx_check_partial_solve_wit_9_matrix_normal_budget_pure :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_matrix_normal_budget)) (PreH2 : (c_pre = C_matrix_normal_budget)) (PreH3 : (inputs_pre = N_matrix_normal_budget)) (PreH4 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH5 : (rows_pre = M_matrix_normal_budget)) (PreH6 : (1 <= M_matrix_normal_budget)) (PreH7 : (M_matrix_normal_budget <= 16)) (PreH8 : (0 <= N_matrix_normal_budget)) (PreH9 : (N_matrix_normal_budget <= 8)) (PreH10 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH13 : (0 <= L_matrix_normal_budget)) (PreH14 : (L_matrix_normal_budget <= INT_MAX)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
  **  (simplex_check_old S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  “ (s_pre = S_matrix_normal_budget) ”
  &&  “ (c_pre = C_matrix_normal_budget) ”
  &&  “ (rows_pre = M_matrix_normal_budget) ”
  &&  “ (inputs_pre = N_matrix_normal_budget) ”
  &&  “ (1 <= M_matrix_normal_budget) ”
  &&  “ (M_matrix_normal_budget <= 16) ”
  &&  “ (0 <= N_matrix_normal_budget) ”
  &&  “ (N_matrix_normal_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget ) ”
.

Definition sx_check_partial_solve_wit_9_matrix_normal_budget_aux :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (PreH1 : (s_pre = S_matrix_normal_budget)) (PreH2 : (c_pre = C_matrix_normal_budget)) (PreH3 : (inputs_pre = N_matrix_normal_budget)) (PreH4 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH5 : (rows_pre = M_matrix_normal_budget)) (PreH6 : (1 <= M_matrix_normal_budget)) (PreH7 : (M_matrix_normal_budget <= 16)) (PreH8 : (0 <= N_matrix_normal_budget)) (PreH9 : (N_matrix_normal_budget <= 8)) (PreH10 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH13 : (0 <= L_matrix_normal_budget)) (PreH14 : (L_matrix_normal_budget <= INT_MAX)),
  (simplex_check_old S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  “ (s_pre = S_matrix_normal_budget) ”
  &&  “ (c_pre = C_matrix_normal_budget) ”
  &&  “ (rows_pre = M_matrix_normal_budget) ”
  &&  “ (inputs_pre = N_matrix_normal_budget) ”
  &&  “ (1 <= M_matrix_normal_budget) ”
  &&  “ (M_matrix_normal_budget <= 16) ”
  &&  “ (0 <= N_matrix_normal_budget) ”
  &&  “ (N_matrix_normal_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget ) ”
  &&  “ (s_pre = S_matrix_normal_budget) ”
  &&  “ (c_pre = C_matrix_normal_budget) ”
  &&  “ (inputs_pre = N_matrix_normal_budget) ”
  &&  “ (pivot_limit_pre = L_matrix_normal_budget) ”
  &&  “ (rows_pre = M_matrix_normal_budget) ”
  &&  “ (1 <= M_matrix_normal_budget) ”
  &&  “ (M_matrix_normal_budget <= 16) ”
  &&  “ (0 <= N_matrix_normal_budget) ”
  &&  “ (N_matrix_normal_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget ) ”
  &&  “ (0 <= L_matrix_normal_budget) ”
  &&  “ (L_matrix_normal_budget <= INT_MAX) ”
  &&  (simplex_check_old S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
.

Definition sx_check_partial_solve_wit_9_matrix_normal_budget := sx_check_partial_solve_wit_9_matrix_normal_budget_pure -> sx_check_partial_solve_wit_9_matrix_normal_budget_aux.

Definition sx_check_partial_solve_wit_10_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
).

Definition sx_check_partial_solve_wit_10_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (M_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
.

Definition sx_check_partial_solve_wit_10_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 0 ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (M_check_invalid_dimensions < 0) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_10_check_invalid_dimensions := sx_check_partial_solve_wit_10_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_10_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_11_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
).

Definition sx_check_partial_solve_wit_11_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (M_check_invalid_dimensions > 16)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
.

Definition sx_check_partial_solve_wit_11_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (M_check_invalid_dimensions > 16)),
  TT && emp 
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 0 ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (M_check_invalid_dimensions > 16) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_11_check_invalid_dimensions := sx_check_partial_solve_wit_11_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_11_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_12_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
).

Definition sx_check_partial_solve_wit_12_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (N_check_invalid_dimensions < 0)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
.

Definition sx_check_partial_solve_wit_12_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions < 0)),
  TT && emp 
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 0 ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (N_check_invalid_dimensions < 0) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_12_check_invalid_dimensions := sx_check_partial_solve_wit_12_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_12_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_13_check_invalid_dimensions_pure :=
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
) \/
(
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
).

Definition sx_check_partial_solve_wit_13_check_invalid_dimensions_pure_split_goal_1 :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_invalid_dimensions)) (PreH10 : (c_pre = C_check_invalid_dimensions)) (PreH11 : (rows_pre = M_check_invalid_dimensions)) (PreH12 : (inputs_pre = N_check_invalid_dimensions)) (PreH13 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH14 : (N_check_invalid_dimensions > 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_invalid_dimensions < 0) ”
.

Definition sx_check_partial_solve_wit_13_check_invalid_dimensions_aux :=
forall (L_check_invalid_dimensions: Z) (C_check_invalid_dimensions: Z) (S_check_invalid_dimensions: Z) (N_check_invalid_dimensions: Z) (M_check_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_invalid_dimensions)) (PreH4 : (c_pre = C_check_invalid_dimensions)) (PreH5 : (rows_pre = M_check_invalid_dimensions)) (PreH6 : (inputs_pre = N_check_invalid_dimensions)) (PreH7 : (pivot_limit_pre = L_check_invalid_dimensions)) (PreH8 : (N_check_invalid_dimensions > 8)),
  TT && emp 
|--
  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (L_check_invalid_dimensions < 0) ”
  &&  “ ((INT_MIN) <= L_check_invalid_dimensions) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 0 ) ”
  &&  “ (s_pre = S_check_invalid_dimensions) ”
  &&  “ (c_pre = C_check_invalid_dimensions) ”
  &&  “ (rows_pre = M_check_invalid_dimensions) ”
  &&  “ (inputs_pre = N_check_invalid_dimensions) ”
  &&  “ (pivot_limit_pre = L_check_invalid_dimensions) ”
  &&  “ (N_check_invalid_dimensions > 8) ”
  &&  emp
.

Definition sx_check_partial_solve_wit_13_check_invalid_dimensions := sx_check_partial_solve_wit_13_check_invalid_dimensions_pure -> sx_check_partial_solve_wit_13_check_invalid_dimensions_aux.

Definition sx_check_partial_solve_wit_14_check_rejected_coefficient_pure :=
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_check_rejected_coefficient) ”
  &&  “ (L_check_rejected_coefficient < 0) ”
  &&  “ ((INT_MIN) <= L_check_rejected_coefficient) ”
) \/
(
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_rejected_coefficient)) (PreH10 : (c_pre = C_check_rejected_coefficient)) (PreH11 : (rows_pre = M_check_rejected_coefficient)) (PreH12 : (inputs_pre = N_check_rejected_coefficient)) (PreH13 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH14 : (0 <= M_check_rejected_coefficient)) (PreH15 : (M_check_rejected_coefficient <= 16)) (PreH16 : (0 <= N_check_rejected_coefficient)) (PreH17 : (N_check_rejected_coefficient <= 8)) (PreH18 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH19 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH20 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH21 : (0 <= x)) (PreH22 : (x < M_check_rejected_coefficient)) (PreH23 : (0 <= y)) (PreH24 : (y <= N_check_rejected_coefficient)) (PreH25 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_rejected_coefficient < 0) ”
).

Definition sx_check_partial_solve_wit_14_check_rejected_coefficient_pure_split_goal_1 :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : (pivot_limit_pre >= INT_MIN)) (PreH5 : (inputs_pre >= INT_MIN)) (PreH6 : (rows_pre >= INT_MIN)) (PreH7 : (retval <> 0)) (PreH8 : (simplex_init_return retval 0 )) (PreH9 : (s_pre = S_check_rejected_coefficient)) (PreH10 : (c_pre = C_check_rejected_coefficient)) (PreH11 : (rows_pre = M_check_rejected_coefficient)) (PreH12 : (inputs_pre = N_check_rejected_coefficient)) (PreH13 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH14 : (0 <= M_check_rejected_coefficient)) (PreH15 : (M_check_rejected_coefficient <= 16)) (PreH16 : (0 <= N_check_rejected_coefficient)) (PreH17 : (N_check_rejected_coefficient <= 8)) (PreH18 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH19 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH20 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH21 : (0 <= x)) (PreH22 : (x < M_check_rejected_coefficient)) (PreH23 : (0 <= y)) (PreH24 : (y <= N_check_rejected_coefficient)) (PreH25 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (L_check_rejected_coefficient < 0) ”
.

Definition sx_check_partial_solve_wit_14_check_rejected_coefficient_aux :=
forall (L_check_rejected_coefficient: Z) (C_check_rejected_coefficient: Z) (S_check_rejected_coefficient: Z) (N_check_rejected_coefficient: Z) (M_check_rejected_coefficient: Z) (A_check_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 0 )) (PreH3 : (s_pre = S_check_rejected_coefficient)) (PreH4 : (c_pre = C_check_rejected_coefficient)) (PreH5 : (rows_pre = M_check_rejected_coefficient)) (PreH6 : (inputs_pre = N_check_rejected_coefficient)) (PreH7 : (pivot_limit_pre = L_check_rejected_coefficient)) (PreH8 : (0 <= M_check_rejected_coefficient)) (PreH9 : (M_check_rejected_coefficient <= 16)) (PreH10 : (0 <= N_check_rejected_coefficient)) (PreH11 : (N_check_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_check_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_check_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN))),
  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
|--
  “ (pivot_limit_pre = L_check_rejected_coefficient) ”
  &&  “ (L_check_rejected_coefficient < 0) ”
  &&  “ ((INT_MIN) <= L_check_rejected_coefficient) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 0 ) ”
  &&  “ (s_pre = S_check_rejected_coefficient) ”
  &&  “ (c_pre = C_check_rejected_coefficient) ”
  &&  “ (rows_pre = M_check_rejected_coefficient) ”
  &&  “ (inputs_pre = N_check_rejected_coefficient) ”
  &&  “ (pivot_limit_pre = L_check_rejected_coefficient) ”
  &&  “ (0 <= M_check_rejected_coefficient) ”
  &&  “ (M_check_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_check_rejected_coefficient) ”
  &&  “ (N_check_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_check_rejected_coefficient)) = (M_check_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_check_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_check_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_check_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_check_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_check_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  (simplex_init_input C_check_rejected_coefficient A_check_rejected_coefficient M_check_rejected_coefficient N_check_rejected_coefficient )
.

Definition sx_check_partial_solve_wit_14_check_rejected_coefficient := sx_check_partial_solve_wit_14_check_rejected_coefficient_pure -> sx_check_partial_solve_wit_14_check_rejected_coefficient_aux.

Definition sx_check_partial_solve_wit_15_zero_negative_budget_pure :=
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_zero_negative_budget) ”
  &&  “ ((INT_MIN) <= L_zero_negative_budget) ”
  &&  “ (L_zero_negative_budget < 0) ”
.

Definition sx_check_partial_solve_wit_15_zero_negative_budget_aux :=
forall (Old_zero_negative_budget: simplex_check_memory_snapshot) (L_zero_negative_budget: Z) (C_zero_negative_budget: Z) (S_zero_negative_budget: Z) (N_zero_negative_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_negative_budget)) (PreH4 : (c_pre = C_zero_negative_budget)) (PreH5 : (inputs_pre = N_zero_negative_budget)) (PreH6 : (pivot_limit_pre = L_zero_negative_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_negative_budget)) (PreH9 : (N_zero_negative_budget <= 8)) (PreH10 : ((INT_MIN) <= L_zero_negative_budget)) (PreH11 : (L_zero_negative_budget < 0)),
  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
|--
  “ (pivot_limit_pre = L_zero_negative_budget) ”
  &&  “ ((INT_MIN) <= L_zero_negative_budget) ”
  &&  “ (L_zero_negative_budget < 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 1 ) ”
  &&  “ (s_pre = S_zero_negative_budget) ”
  &&  “ (c_pre = C_zero_negative_budget) ”
  &&  “ (inputs_pre = N_zero_negative_budget) ”
  &&  “ (pivot_limit_pre = L_zero_negative_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (0 <= N_zero_negative_budget) ”
  &&  “ (N_zero_negative_budget <= 8) ”
  &&  “ ((INT_MIN) <= L_zero_negative_budget) ”
  &&  “ (L_zero_negative_budget < 0) ”
  &&  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_negative_budget)
  **  ((&((S_zero_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_negative_budget ))
  **  (simplex_init_vars S_zero_negative_budget N_zero_negative_budget (0 + N_zero_negative_budget ) 0 (0 + N_zero_negative_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_negative_budget (@nil Z) N_zero_negative_budget 0 0 (0 + N_zero_negative_budget ) )
  **  (simplex_check_frame S_zero_negative_budget 0 N_zero_negative_budget Old_zero_negative_budget )
.

Definition sx_check_partial_solve_wit_15_zero_negative_budget := sx_check_partial_solve_wit_15_zero_negative_budget_pure -> sx_check_partial_solve_wit_15_zero_negative_budget_aux.

Definition sx_check_partial_solve_wit_16_zero_normal_budget_pure :=
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_normal_budget)) (PreH4 : (c_pre = C_zero_normal_budget)) (PreH5 : (inputs_pre = N_zero_normal_budget)) (PreH6 : (pivot_limit_pre = L_zero_normal_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_normal_budget)) (PreH9 : (N_zero_normal_budget <= 8)) (PreH10 : (0 <= L_zero_normal_budget)) (PreH11 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (s_pre = S_zero_normal_budget) ”
  &&  “ (pivot_limit_pre = L_zero_normal_budget) ”
  &&  “ (0 <= L_zero_normal_budget) ”
  &&  “ (L_zero_normal_budget <= INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_normal_budget) ”
  &&  “ (N_zero_normal_budget <= 8) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < 0)) /\ (0 <= j)) /\ (j <= N_zero_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) ((@nil Z)) (0))) /\ ((Znth (((i * 9 ) + j )) ((@nil Z)) (0)) <= INT_MAX))) ”
) \/
(
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : ((0 + N_zero_normal_budget ) <= INT_MAX)) (PreH5 : (N_zero_normal_budget <= INT_MAX)) (PreH6 : (0 <= INT_MAX)) (PreH7 : (pivot_limit_pre >= INT_MIN)) (PreH8 : (inputs_pre >= INT_MIN)) (PreH9 : (rows_pre >= INT_MIN)) (PreH10 : ((0 + N_zero_normal_budget ) >= INT_MIN)) (PreH11 : (N_zero_normal_budget >= INT_MIN)) (PreH12 : (0 >= INT_MIN)) (PreH13 : (retval <> 0)) (PreH14 : (simplex_init_return retval 1 )) (PreH15 : (s_pre = S_zero_normal_budget)) (PreH16 : (c_pre = C_zero_normal_budget)) (PreH17 : (inputs_pre = N_zero_normal_budget)) (PreH18 : (pivot_limit_pre = L_zero_normal_budget)) (PreH19 : (rows_pre = 0)) (PreH20 : (0 <= N_zero_normal_budget)) (PreH21 : (N_zero_normal_budget <= 8)) (PreH22 : (0 <= L_zero_normal_budget)) (PreH23 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < 0)) /\ (0 <= j)) /\ (j <= N_zero_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) ((@nil Z)) (0))) /\ ((Znth (((i * 9 ) + j )) ((@nil Z)) (0)) <= INT_MAX))) ”
).

Definition sx_check_partial_solve_wit_16_zero_normal_budget_pure_split_goal_1 :=
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : ((0 + N_zero_normal_budget ) <= INT_MAX)) (PreH5 : (N_zero_normal_budget <= INT_MAX)) (PreH6 : (0 <= INT_MAX)) (PreH7 : (pivot_limit_pre >= INT_MIN)) (PreH8 : (inputs_pre >= INT_MIN)) (PreH9 : (rows_pre >= INT_MIN)) (PreH10 : ((0 + N_zero_normal_budget ) >= INT_MIN)) (PreH11 : (N_zero_normal_budget >= INT_MIN)) (PreH12 : (0 >= INT_MIN)) (PreH13 : (retval <> 0)) (PreH14 : (simplex_init_return retval 1 )) (PreH15 : (s_pre = S_zero_normal_budget)) (PreH16 : (c_pre = C_zero_normal_budget)) (PreH17 : (inputs_pre = N_zero_normal_budget)) (PreH18 : (pivot_limit_pre = L_zero_normal_budget)) (PreH19 : (rows_pre = 0)) (PreH20 : (0 <= N_zero_normal_budget)) (PreH21 : (N_zero_normal_budget <= 8)) (PreH22 : (0 <= L_zero_normal_budget)) (PreH23 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < 0)) /\ (0 <= j)) /\ (j <= N_zero_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) ((@nil Z)) (0))) /\ ((Znth (((i * 9 ) + j )) ((@nil Z)) (0)) <= INT_MAX))) ”
.

Definition sx_check_partial_solve_wit_16_zero_normal_budget_aux :=
forall (Old_zero_normal_budget: simplex_check_memory_snapshot) (L_zero_normal_budget: Z) (C_zero_normal_budget: Z) (S_zero_normal_budget: Z) (N_zero_normal_budget: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_zero_normal_budget)) (PreH4 : (c_pre = C_zero_normal_budget)) (PreH5 : (inputs_pre = N_zero_normal_budget)) (PreH6 : (pivot_limit_pre = L_zero_normal_budget)) (PreH7 : (rows_pre = 0)) (PreH8 : (0 <= N_zero_normal_budget)) (PreH9 : (N_zero_normal_budget <= 8)) (PreH10 : (0 <= L_zero_normal_budget)) (PreH11 : (L_zero_normal_budget <= INT_MAX)),
  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
|--
  “ (s_pre = S_zero_normal_budget) ”
  &&  “ (pivot_limit_pre = L_zero_normal_budget) ”
  &&  “ (0 <= L_zero_normal_budget) ”
  &&  “ (L_zero_normal_budget <= INT_MAX) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_normal_budget) ”
  &&  “ (N_zero_normal_budget <= 8) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < 0)) /\ (0 <= j)) /\ (j <= N_zero_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) ((@nil Z)) (0))) /\ ((Znth (((i * 9 ) + j )) ((@nil Z)) (0)) <= INT_MAX))) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 1 ) ”
  &&  “ (s_pre = S_zero_normal_budget) ”
  &&  “ (c_pre = C_zero_normal_budget) ”
  &&  “ (inputs_pre = N_zero_normal_budget) ”
  &&  “ (pivot_limit_pre = L_zero_normal_budget) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (0 <= N_zero_normal_budget) ”
  &&  “ (N_zero_normal_budget <= 8) ”
  &&  “ (0 <= L_zero_normal_budget) ”
  &&  “ (L_zero_normal_budget <= INT_MAX) ”
  &&  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_normal_budget)
  **  ((&((S_zero_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_normal_budget ))
  **  (simplex_init_vars S_zero_normal_budget N_zero_normal_budget (0 + N_zero_normal_budget ) 0 (0 + N_zero_normal_budget ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_normal_budget (@nil Z) N_zero_normal_budget 0 0 (0 + N_zero_normal_budget ) )
  **  (simplex_check_frame S_zero_normal_budget 0 N_zero_normal_budget Old_zero_normal_budget )
.

Definition sx_check_partial_solve_wit_16_zero_normal_budget := sx_check_partial_solve_wit_16_zero_normal_budget_pure -> sx_check_partial_solve_wit_16_zero_normal_budget_aux.

Definition sx_check_partial_solve_wit_17_matrix_negative_budget_pure :=
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (pivot_limit_pre = L_matrix_negative_budget) ”
  &&  “ ((INT_MIN) <= L_matrix_negative_budget) ”
  &&  “ (L_matrix_negative_budget < 0) ”
.

Definition sx_check_partial_solve_wit_17_matrix_negative_budget_aux :=
forall (CO_matrix_negative_budget: simplex_check_memory_snapshot) (Old_matrix_negative_budget: simplex_check_memory_snapshot) (L_matrix_negative_budget: Z) (C_matrix_negative_budget: Z) (S_matrix_negative_budget: Z) (N_matrix_negative_budget: Z) (M_matrix_negative_budget: Z) (A_matrix_negative_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_negative_budget)) (PreH4 : (c_pre = C_matrix_negative_budget)) (PreH5 : (inputs_pre = N_matrix_negative_budget)) (PreH6 : (pivot_limit_pre = L_matrix_negative_budget)) (PreH7 : (rows_pre = M_matrix_negative_budget)) (PreH8 : (1 <= M_matrix_negative_budget)) (PreH9 : (M_matrix_negative_budget <= 16)) (PreH10 : (0 <= N_matrix_negative_budget)) (PreH11 : (N_matrix_negative_budget <= 8)) (PreH12 : ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget )) (PreH15 : ((INT_MIN) <= L_matrix_negative_budget)) (PreH16 : (L_matrix_negative_budget < 0)),
  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
|--
  “ (pivot_limit_pre = L_matrix_negative_budget) ”
  &&  “ ((INT_MIN) <= L_matrix_negative_budget) ”
  &&  “ (L_matrix_negative_budget < 0) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 1 ) ”
  &&  “ (s_pre = S_matrix_negative_budget) ”
  &&  “ (c_pre = C_matrix_negative_budget) ”
  &&  “ (inputs_pre = N_matrix_negative_budget) ”
  &&  “ (pivot_limit_pre = L_matrix_negative_budget) ”
  &&  “ (rows_pre = M_matrix_negative_budget) ”
  &&  “ (1 <= M_matrix_negative_budget) ”
  &&  “ (M_matrix_negative_budget <= 16) ”
  &&  “ (0 <= N_matrix_negative_budget) ”
  &&  “ (N_matrix_negative_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_negative_budget)) = (M_matrix_negative_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_negative_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_negative_budget ) ”
  &&  “ ((INT_MIN) <= L_matrix_negative_budget) ”
  &&  “ (L_matrix_negative_budget < 0) ”
  &&  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_negative_budget)
  **  ((&((S_matrix_negative_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_negative_budget + N_matrix_negative_budget ))
  **  (simplex_init_vars S_matrix_negative_budget N_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) (simplex_init_rhs (A_matrix_negative_budget) (M_matrix_negative_budget)) 1 )
  **  (simplex_init_rows S_matrix_negative_budget A_matrix_negative_budget N_matrix_negative_budget M_matrix_negative_budget M_matrix_negative_budget (M_matrix_negative_budget + N_matrix_negative_budget ) )
  **  (simplex_check_frame S_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget Old_matrix_negative_budget )
  **  (simplex_init_input C_matrix_negative_budget A_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget )
  **  (simplex_check_input_frame C_matrix_negative_budget M_matrix_negative_budget N_matrix_negative_budget CO_matrix_negative_budget )
.

Definition sx_check_partial_solve_wit_17_matrix_negative_budget := sx_check_partial_solve_wit_17_matrix_negative_budget_pure -> sx_check_partial_solve_wit_17_matrix_negative_budget_aux.

Definition sx_check_partial_solve_wit_18_matrix_normal_budget_pure :=
(
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_normal_budget)) (PreH4 : (c_pre = C_matrix_normal_budget)) (PreH5 : (inputs_pre = N_matrix_normal_budget)) (PreH6 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH7 : (rows_pre = M_matrix_normal_budget)) (PreH8 : (1 <= M_matrix_normal_budget)) (PreH9 : (M_matrix_normal_budget <= 16)) (PreH10 : (0 <= N_matrix_normal_budget)) (PreH11 : (N_matrix_normal_budget <= 8)) (PreH12 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH15 : (0 <= L_matrix_normal_budget)) (PreH16 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ (s_pre = S_matrix_normal_budget) ”
  &&  “ (pivot_limit_pre = L_matrix_normal_budget) ”
  &&  “ (0 <= L_matrix_normal_budget) ”
  &&  “ (L_matrix_normal_budget <= INT_MAX) ”
  &&  “ (0 <= M_matrix_normal_budget) ”
  &&  “ (M_matrix_normal_budget <= 16) ”
  &&  “ (0 <= N_matrix_normal_budget) ”
  &&  “ (N_matrix_normal_budget <= 8) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_matrix_normal_budget)) /\ (0 <= j)) /\ (j <= N_matrix_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0))) /\ ((Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0)) <= INT_MAX))) ”
) \/
(
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : ((M_matrix_normal_budget + N_matrix_normal_budget ) <= INT_MAX)) (PreH5 : (N_matrix_normal_budget <= INT_MAX)) (PreH6 : (M_matrix_normal_budget <= INT_MAX)) (PreH7 : (pivot_limit_pre >= INT_MIN)) (PreH8 : (inputs_pre >= INT_MIN)) (PreH9 : (rows_pre >= INT_MIN)) (PreH10 : ((M_matrix_normal_budget + N_matrix_normal_budget ) >= INT_MIN)) (PreH11 : (N_matrix_normal_budget >= INT_MIN)) (PreH12 : (M_matrix_normal_budget >= INT_MIN)) (PreH13 : (retval <> 0)) (PreH14 : (simplex_init_return retval 1 )) (PreH15 : (s_pre = S_matrix_normal_budget)) (PreH16 : (c_pre = C_matrix_normal_budget)) (PreH17 : (inputs_pre = N_matrix_normal_budget)) (PreH18 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH19 : (rows_pre = M_matrix_normal_budget)) (PreH20 : (1 <= M_matrix_normal_budget)) (PreH21 : (M_matrix_normal_budget <= 16)) (PreH22 : (0 <= N_matrix_normal_budget)) (PreH23 : (N_matrix_normal_budget <= 8)) (PreH24 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH25 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH26 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH27 : (0 <= L_matrix_normal_budget)) (PreH28 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_matrix_normal_budget)) /\ (0 <= j)) /\ (j <= N_matrix_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0))) /\ ((Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0)) <= INT_MAX))) ”
).

Definition sx_check_partial_solve_wit_18_matrix_normal_budget_pure_split_goal_1 :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (pivot_limit_pre <= INT_MAX)) (PreH2 : (inputs_pre <= INT_MAX)) (PreH3 : (rows_pre <= INT_MAX)) (PreH4 : ((M_matrix_normal_budget + N_matrix_normal_budget ) <= INT_MAX)) (PreH5 : (N_matrix_normal_budget <= INT_MAX)) (PreH6 : (M_matrix_normal_budget <= INT_MAX)) (PreH7 : (pivot_limit_pre >= INT_MIN)) (PreH8 : (inputs_pre >= INT_MIN)) (PreH9 : (rows_pre >= INT_MIN)) (PreH10 : ((M_matrix_normal_budget + N_matrix_normal_budget ) >= INT_MIN)) (PreH11 : (N_matrix_normal_budget >= INT_MIN)) (PreH12 : (M_matrix_normal_budget >= INT_MIN)) (PreH13 : (retval <> 0)) (PreH14 : (simplex_init_return retval 1 )) (PreH15 : (s_pre = S_matrix_normal_budget)) (PreH16 : (c_pre = C_matrix_normal_budget)) (PreH17 : (inputs_pre = N_matrix_normal_budget)) (PreH18 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH19 : (rows_pre = M_matrix_normal_budget)) (PreH20 : (1 <= M_matrix_normal_budget)) (PreH21 : (M_matrix_normal_budget <= 16)) (PreH22 : (0 <= N_matrix_normal_budget)) (PreH23 : (N_matrix_normal_budget <= 8)) (PreH24 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH25 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH26 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH27 : (0 <= L_matrix_normal_budget)) (PreH28 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "pivot_limit" ) )) # Int  |-> pivot_limit_pre)
|--
  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_matrix_normal_budget)) /\ (0 <= j)) /\ (j <= N_matrix_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0))) /\ ((Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0)) <= INT_MAX))) ”
.

Definition sx_check_partial_solve_wit_18_matrix_normal_budget_aux :=
forall (CO_matrix_normal_budget: simplex_check_memory_snapshot) (Old_matrix_normal_budget: simplex_check_memory_snapshot) (L_matrix_normal_budget: Z) (C_matrix_normal_budget: Z) (S_matrix_normal_budget: Z) (N_matrix_normal_budget: Z) (M_matrix_normal_budget: Z) (A_matrix_normal_budget: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (pivot_limit_pre: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (simplex_init_return retval 1 )) (PreH3 : (s_pre = S_matrix_normal_budget)) (PreH4 : (c_pre = C_matrix_normal_budget)) (PreH5 : (inputs_pre = N_matrix_normal_budget)) (PreH6 : (pivot_limit_pre = L_matrix_normal_budget)) (PreH7 : (rows_pre = M_matrix_normal_budget)) (PreH8 : (1 <= M_matrix_normal_budget)) (PreH9 : (M_matrix_normal_budget <= 16)) (PreH10 : (0 <= N_matrix_normal_budget)) (PreH11 : (N_matrix_normal_budget <= 8)) (PreH12 : ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget )) (PreH15 : (0 <= L_matrix_normal_budget)) (PreH16 : (L_matrix_normal_budget <= INT_MAX)),
  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
|--
  “ (s_pre = S_matrix_normal_budget) ”
  &&  “ (pivot_limit_pre = L_matrix_normal_budget) ”
  &&  “ (0 <= L_matrix_normal_budget) ”
  &&  “ (L_matrix_normal_budget <= INT_MAX) ”
  &&  “ (0 <= M_matrix_normal_budget) ”
  &&  “ (M_matrix_normal_budget <= 16) ”
  &&  “ (0 <= N_matrix_normal_budget) ”
  &&  “ (N_matrix_normal_budget <= 8) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_matrix_normal_budget)) /\ (0 <= j)) /\ (j <= N_matrix_normal_budget)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0))) /\ ((Znth (((i * 9 ) + j )) (A_matrix_normal_budget) (0)) <= INT_MAX))) ”
  &&  “ (retval <> 0) ”
  &&  “ (simplex_init_return retval 1 ) ”
  &&  “ (s_pre = S_matrix_normal_budget) ”
  &&  “ (c_pre = C_matrix_normal_budget) ”
  &&  “ (inputs_pre = N_matrix_normal_budget) ”
  &&  “ (pivot_limit_pre = L_matrix_normal_budget) ”
  &&  “ (rows_pre = M_matrix_normal_budget) ”
  &&  “ (1 <= M_matrix_normal_budget) ”
  &&  “ (M_matrix_normal_budget <= 16) ”
  &&  “ (0 <= N_matrix_normal_budget) ”
  &&  “ (N_matrix_normal_budget <= 8) ”
  &&  “ ((Zlength (A_matrix_normal_budget)) = (M_matrix_normal_budget * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_matrix_normal_budget ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_matrix_normal_budget ) ”
  &&  “ (0 <= L_matrix_normal_budget) ”
  &&  “ (L_matrix_normal_budget <= INT_MAX) ”
  &&  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "rows")) # Int  |-> M_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "inputs")) # Int  |-> N_matrix_normal_budget)
  **  ((&((S_matrix_normal_budget)  # "SxState" ->ₛ "vars")) # Int  |-> (M_matrix_normal_budget + N_matrix_normal_budget ))
  **  (simplex_init_vars S_matrix_normal_budget N_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) (simplex_init_rhs (A_matrix_normal_budget) (M_matrix_normal_budget)) 1 )
  **  (simplex_init_rows S_matrix_normal_budget A_matrix_normal_budget N_matrix_normal_budget M_matrix_normal_budget M_matrix_normal_budget (M_matrix_normal_budget + N_matrix_normal_budget ) )
  **  (simplex_check_frame S_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget Old_matrix_normal_budget )
  **  (simplex_init_input C_matrix_normal_budget A_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget )
  **  (simplex_check_input_frame C_matrix_normal_budget M_matrix_normal_budget N_matrix_normal_budget CO_matrix_normal_budget )
.

Definition sx_check_partial_solve_wit_18_matrix_normal_budget := sx_check_partial_solve_wit_18_matrix_normal_budget_pure -> sx_check_partial_solve_wit_18_matrix_normal_budget_aux.

(* Shallow FunAssertion specs for sx_solve. *)
Definition sx_solve_sig : FuncSig := ([ * struct "SxState"; i32], i32)%ctype.

Definition sx_solve_check_solve_initialized : Spec sx_solve_sig :=
  fun F =>
ALL (S: Z),
ALL (L: Z),
ALL (M: Z),
ALL (N: Z),
ALL (A: (@list Z)),
HoareFun ([ * struct "SxState"; i32], i32)%ctype
  (fun '(s_pre, pivot_limit_pre) =>
  (“ (s_pre = S) ”
  &&  “ (pivot_limit_pre = L) ”
  &&  “ (0 <= L) ”
  &&  “ (L <= INT_MAX) ”
  &&  “ (0 <= M) ”
  &&  “ (M <= 16) ”
  &&  “ (0 <= N) ”
  &&  “ (N <= 8) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M)) /\ (0 <= j)) /\ (j <= N)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A) (0))) /\ ((Znth (((i * 9 ) + j )) (A) (0)) <= INT_MAX))) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (M + N ))
  **  (simplex_init_vars S N (M + N ) M (M + N ) (simplex_init_rhs (A) (M)) 1 )
  **  (simplex_init_rows S A N M M (M + N ) )))
  (fun '(s_pre, pivot_limit_pre) retval =>
(orp
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 1) ”
  &&  “ (simplex_check_result A M N L retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A M N OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A M N )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) M N (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) M N (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (M + N ))
  **  (IntArray.full &((S)  # "SxState" ->ₛ "basic") M OB )
  **  (IntArray.full &((S)  # "SxState" ->ₛ "is_basic") (M + N ) OIB )
  **  (simplex_pivot_memory S M (M + N ) ON OD )
  **  (simplex_solve_variables S (M + N ) (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) OVN OVD (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) ))
(orp
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 0) ”
  &&  “ (simplex_check_result A M N L retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A M N OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A M N )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) M N (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) M N (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (M + N ))
  **  (IntArray.full &((S)  # "SxState" ->ₛ "basic") M OB )
  **  (IntArray.full &((S)  # "SxState" ->ₛ "is_basic") (M + N ) OIB )
  **  (simplex_pivot_memory S M (M + N ) ON OD )
  **  (simplex_solve_variables S (M + N ) (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) OVN OVD (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) ))
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = (-1)) ”
  &&  “ (simplex_check_result A M N L retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A M N OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A M N )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) M N (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) M N (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (M + N ))
  **  (IntArray.full &((S)  # "SxState" ->ₛ "basic") M OB )
  **  (IntArray.full &((S)  # "SxState" ->ₛ "is_basic") (M + N ) OIB )
  **  (simplex_pivot_memory S M (M + N ) ON OD )
  **  (simplex_solve_variables S (M + N ) (simplex_init_zeroes ((M + N ))) (simplex_init_flags (N) ((M + N ))) OVN OVD (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) (simplex_init_zeroes ((M + N ))) (simplex_init_ones ((M + N ))) )))))
  F.

Definition sx_solve_negative_budget : Spec sx_solve_sig :=
  fun F =>
ALL (L: Z),
HoareFun ([ * struct "SxState"; i32], i32)%ctype
  (fun '(s_pre, pivot_limit_pre) =>
  (“ (pivot_limit_pre = L) ”
  &&  “ ((INT_MIN) <= L) ”
  &&  “ (L < 0) ”
  &&  emp))
  (fun '(s_pre, pivot_limit_pre) retval =>
  (“ (retval = (-1)) ”
  &&  emp))
  F.

Definition sx_solve_normal_state : Spec sx_solve_sig :=
  fun F =>
ALL (S: Z),
ALL (L: Z),
ALL (M: Z),
ALL (I: Z),
ALL (V: Z),
ALL (A: (@list Z)),
ALL (N: (@list Z)),
ALL (D: (@list Z)),
ALL (B: (@list Z)),
ALL (IB: (@list Z)),
ALL (HL: (@list Z)),
ALL (HU: (@list Z)),
ALL (LN: (@list Z)),
ALL (LD: (@list Z)),
ALL (UN: (@list Z)),
ALL (UD: (@list Z)),
ALL (VN: (@list Z)),
ALL (VD: (@list Z)),
HoareFun ([ * struct "SxState"; i32], i32)%ctype
  (fun '(s_pre, pivot_limit_pre) =>
  (“ (s_pre = S) ”
  &&  “ (pivot_limit_pre = L) ”
  &&  “ (0 <= L) ”
  &&  “ (L <= INT_MAX) ”
  &&  “ (0 <= M) ”
  &&  “ (M <= 16) ”
  &&  “ (0 <= I) ”
  &&  “ (I <= 8) ”
  &&  “ (V = (M + I )) ”
  &&  “ (0 <= V) ”
  &&  “ (V <= 24) ”
  &&  “ ((Zlength (N)) = 400) ”
  &&  “ ((Zlength (D)) = 400) ”
  &&  “ ((Zlength (B)) = M) ”
  &&  “ ((Zlength (IB)) = V) ”
  &&  “ ((Zlength (HL)) = V) ”
  &&  “ ((Zlength (HU)) = V) ”
  &&  “ ((Zlength (LN)) = V) ”
  &&  “ ((Zlength (LD)) = V) ”
  &&  “ ((Zlength (UN)) = V) ”
  &&  “ ((Zlength (UD)) = V) ”
  &&  “ ((Zlength (VN)) = V) ”
  &&  “ ((Zlength (VD)) = V) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M)) /\ (0 <= j)) /\ (j <= I)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A) (0))) /\ ((Znth (((i * 9 ) + j )) (A) (0)) <= INT_MAX))) ”
  &&  “ (simplex_solve_normal A HL HU LN LD UN UD M I (simplex_solve_pack (N) (D) (B) (IB) (VN) (VD)) ) ”
  &&  “ (simplex_solve_origin A HL HU LN LD UN UD M I (simplex_solve_pack (N) (D) (B) (IB) (VN) (VD)) ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M B )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V IB )
  **  (simplex_pivot_memory s_pre M V N D )
  **  (simplex_solve_variables s_pre V HL HU VN VD LN LD UN UD )))
  (fun '(s_pre, pivot_limit_pre) retval =>
(orp
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 1) ”
  &&  “ (simplex_solve_result HL HU LN LD UN UD M V L N D B IB VN VD retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A HL HU LN LD UN UD M I (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A HL HU LN LD UN UD M I (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A M I OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A M I )) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> V)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> I)
  **  (IntArray.full &((S)  # "SxState" ->ₛ "basic") M OB )
  **  (IntArray.full &((S)  # "SxState" ->ₛ "is_basic") V OIB )
  **  (simplex_pivot_memory S M V ON OD )
  **  (simplex_solve_variables S V HL HU OVN OVD LN LD UN UD ))
(orp
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 0) ”
  &&  “ (simplex_solve_result HL HU LN LD UN UD M V L N D B IB VN VD retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A HL HU LN LD UN UD M I (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A HL HU LN LD UN UD M I (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A M I OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A M I )) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> V)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> I)
  **  (IntArray.full &((S)  # "SxState" ->ₛ "basic") M OB )
  **  (IntArray.full &((S)  # "SxState" ->ₛ "is_basic") V OIB )
  **  (simplex_pivot_memory S M V ON OD )
  **  (simplex_solve_variables S V HL HU OVN OVD LN LD UN UD ))
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = (-1)) ”
  &&  “ (simplex_solve_result HL HU LN LD UN UD M V L N D B IB VN VD retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A HL HU LN LD UN UD M I (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A HL HU LN LD UN UD M I (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A M I OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A M I )) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> V)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> I)
  **  (IntArray.full &((S)  # "SxState" ->ₛ "basic") M OB )
  **  (IntArray.full &((S)  # "SxState" ->ₛ "is_basic") V OIB )
  **  (simplex_pivot_memory S M V ON OD )
  **  (simplex_solve_variables S V HL HU OVN OVD LN LD UN UD )))))
  F.

Definition sx_solve_normal_state_entail_check_solve_initialized :=
forall (s_pre: Z) (pivot_limit_pre: Z) (S_check_solve_initialized: Z) (L_check_solve_initialized: Z) (M_check_solve_initialized: Z) (N_check_solve_initialized: Z) (A_check_solve_initialized: (@list Z)),
  (“ (s_pre = S_check_solve_initialized) ”
  &&  “ (pivot_limit_pre = L_check_solve_initialized) ”
  &&  “ (0 <= L_check_solve_initialized) ”
  &&  “ (L_check_solve_initialized <= INT_MAX) ”
  &&  “ (0 <= M_check_solve_initialized) ”
  &&  “ (M_check_solve_initialized <= 16) ”
  &&  “ (0 <= N_check_solve_initialized) ”
  &&  “ (N_check_solve_initialized <= 8) ”
  &&  “ forall (i: Z), forall (j: Z), (((((0 <= i) /\ (i < M_check_solve_initialized)) /\ (0 <= j)) /\ (j <= N_check_solve_initialized)) -> (((-INT_MAX) <= (Znth (((i * 9 ) + j )) (A_check_solve_initialized) (0))) /\ ((Znth (((i * 9 ) + j )) (A_check_solve_initialized) (0)) <= INT_MAX))) ”
  &&  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "rows")) # Int  |-> M_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "inputs")) # Int  |-> N_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "vars")) # Int  |-> (M_check_solve_initialized + N_check_solve_initialized ))
  **  (simplex_init_vars S_check_solve_initialized N_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) M_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) (simplex_init_rhs (A_check_solve_initialized) (M_check_solve_initialized)) 1 )
  **  (simplex_init_rows S_check_solve_initialized A_check_solve_initialized N_check_solve_initialized M_check_solve_initialized M_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) ))
|--
EX (S_normal_state: Z)(L_normal_state: Z)(M_normal_state: Z)(I_normal_state: Z)(V_normal_state: Z)(A_normal_state: (@list Z))(N_normal_state: (@list Z))(D_normal_state: (@list Z))(B_normal_state: (@list Z))(IB_normal_state: (@list Z))(HL_normal_state: (@list Z))(HU_normal_state: (@list Z))(LN_normal_state: (@list Z))(LD_normal_state: (@list Z))(UN_normal_state: (@list Z))(UD_normal_state: (@list Z))(VN_normal_state: (@list Z))(VD_normal_state: (@list Z)),
  (“ (s_pre = S_normal_state) ”
  &&  “ (pivot_limit_pre = L_normal_state) ”
  &&  “ (0 <= L_normal_state) ”
  &&  “ (L_normal_state <= INT_MAX) ”
  &&  “ (0 <= M_normal_state) ”
  &&  “ (M_normal_state <= 16) ”
  &&  “ (0 <= I_normal_state) ”
  &&  “ (I_normal_state <= 8) ”
  &&  “ (V_normal_state = (M_normal_state + I_normal_state )) ”
  &&  “ (0 <= V_normal_state) ”
  &&  “ (V_normal_state <= 24) ”
  &&  “ ((Zlength (N_normal_state)) = 400) ”
  &&  “ ((Zlength (D_normal_state)) = 400) ”
  &&  “ ((Zlength (B_normal_state)) = M_normal_state) ”
  &&  “ ((Zlength (IB_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (HL_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (HU_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (LN_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (LD_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (UN_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (UD_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (VN_normal_state)) = V_normal_state) ”
  &&  “ ((Zlength (VD_normal_state)) = V_normal_state) ”
  &&  “ forall (i_2: Z), forall (j_2: Z), (((((0 <= i_2) /\ (i_2 < M_normal_state)) /\ (0 <= j_2)) /\ (j_2 <= I_normal_state)) -> (((-INT_MAX) <= (Znth (((i_2 * 9 ) + j_2 )) (A_normal_state) (0))) /\ ((Znth (((i_2 * 9 ) + j_2 )) (A_normal_state) (0)) <= INT_MAX))) ”
  &&  “ (simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) ) ”
  &&  “ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (N_normal_state) (D_normal_state) (B_normal_state) (IB_normal_state) (VN_normal_state) (VD_normal_state)) ) ”
  &&  ((&((s_pre)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((s_pre)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "basic") M_normal_state B_normal_state )
  **  (IntArray.full &((s_pre)  # "SxState" ->ₛ "is_basic") V_normal_state IB_normal_state )
  **  (simplex_pivot_memory s_pre M_normal_state V_normal_state N_normal_state D_normal_state )
  **  (simplex_solve_variables s_pre V_normal_state HL_normal_state HU_normal_state VN_normal_state VD_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state ))
  **
  (ALL (retval: Z),
(orp
  (EX (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)),
  “ (retval = 1) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 ) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ))) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN_2 OVD_2 )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB_2 )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB_2 )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON_2 OD_2 )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN_2 OVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state ))
(orp
  (EX (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)),
  “ (retval = 0) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 ) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ))) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN_2 OVD_2 )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB_2 )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB_2 )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON_2 OD_2 )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN_2 OVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state ))
  (EX (ON_2: (@list Z)) (OD_2: (@list Z)) (OB_2: (@list Z)) (OIB_2: (@list Z)) (OVN_2: (@list Z)) (OVD_2: (@list Z)),
  “ (retval = (-1)) ”
  &&  “ (simplex_solve_result HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state V_normal_state L_normal_state N_normal_state D_normal_state B_normal_state IB_normal_state VN_normal_state VD_normal_state retval ON_2 OD_2 OB_2 OIB_2 OVN_2 OVD_2 ) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ) /\ (simplex_solve_origin A_normal_state HL_normal_state HU_normal_state LN_normal_state LD_normal_state UN_normal_state UD_normal_state M_normal_state I_normal_state (simplex_solve_pack (ON_2) (OD_2) (OB_2) (OIB_2) (OVN_2) (OVD_2)) ))) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_normal_state M_normal_state I_normal_state OVN_2 OVD_2 )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_normal_state M_normal_state I_normal_state )) ”
  &&  ((&((S_normal_state)  # "SxState" ->ₛ "rows")) # Int  |-> M_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "vars")) # Int  |-> V_normal_state)
  **  ((&((S_normal_state)  # "SxState" ->ₛ "inputs")) # Int  |-> I_normal_state)
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "basic") M_normal_state OB_2 )
  **  (IntArray.full &((S_normal_state)  # "SxState" ->ₛ "is_basic") V_normal_state OIB_2 )
  **  (simplex_pivot_memory S_normal_state M_normal_state V_normal_state ON_2 OD_2 )
  **  (simplex_solve_variables S_normal_state V_normal_state HL_normal_state HU_normal_state OVN_2 OVD_2 LN_normal_state LD_normal_state UN_normal_state UD_normal_state ))))
  -*
(orp
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 1) ”
  &&  “ (simplex_check_result A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized L_check_solve_initialized retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_check_solve_initialized (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) M_check_solve_initialized N_check_solve_initialized (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_check_solve_initialized (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) M_check_solve_initialized N_check_solve_initialized (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "rows")) # Int  |-> M_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "inputs")) # Int  |-> N_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "vars")) # Int  |-> (M_check_solve_initialized + N_check_solve_initialized ))
  **  (IntArray.full &((S_check_solve_initialized)  # "SxState" ->ₛ "basic") M_check_solve_initialized OB )
  **  (IntArray.full &((S_check_solve_initialized)  # "SxState" ->ₛ "is_basic") (M_check_solve_initialized + N_check_solve_initialized ) OIB )
  **  (simplex_pivot_memory S_check_solve_initialized M_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) ON OD )
  **  (simplex_solve_variables S_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) OVN OVD (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) ))
(orp
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = 0) ”
  &&  “ (simplex_check_result A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized L_check_solve_initialized retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_check_solve_initialized (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) M_check_solve_initialized N_check_solve_initialized (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_check_solve_initialized (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) M_check_solve_initialized N_check_solve_initialized (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "rows")) # Int  |-> M_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "inputs")) # Int  |-> N_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "vars")) # Int  |-> (M_check_solve_initialized + N_check_solve_initialized ))
  **  (IntArray.full &((S_check_solve_initialized)  # "SxState" ->ₛ "basic") M_check_solve_initialized OB )
  **  (IntArray.full &((S_check_solve_initialized)  # "SxState" ->ₛ "is_basic") (M_check_solve_initialized + N_check_solve_initialized ) OIB )
  **  (simplex_pivot_memory S_check_solve_initialized M_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) ON OD )
  **  (simplex_solve_variables S_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) OVN OVD (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) ))
  (EX (ON: (@list Z)) (OD: (@list Z)) (OB: (@list Z)) (OIB: (@list Z)) (OVN: (@list Z)) (OVD: (@list Z)),
  “ (retval = (-1)) ”
  &&  “ (simplex_check_result A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized L_check_solve_initialized retval ON OD OB OIB OVN OVD ) ”
  &&  “ ((retval = 0) -> (simplex_solve_witness A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized OVN OVD )) ”
  &&  “ ((retval = 1) -> (simplex_solve_unsat A_check_solve_initialized M_check_solve_initialized N_check_solve_initialized )) ”
  &&  “ ((retval <> (-1)) -> ((simplex_solve_normal A_check_solve_initialized (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) M_check_solve_initialized N_check_solve_initialized (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ) /\ (simplex_solve_origin A_check_solve_initialized (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) M_check_solve_initialized N_check_solve_initialized (simplex_solve_pack (ON) (OD) (OB) (OIB) (OVN) (OVD)) ))) ”
  &&  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "rows")) # Int  |-> M_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "inputs")) # Int  |-> N_check_solve_initialized)
  **  ((&((S_check_solve_initialized)  # "SxState" ->ₛ "vars")) # Int  |-> (M_check_solve_initialized + N_check_solve_initialized ))
  **  (IntArray.full &((S_check_solve_initialized)  # "SxState" ->ₛ "basic") M_check_solve_initialized OB )
  **  (IntArray.full &((S_check_solve_initialized)  # "SxState" ->ₛ "is_basic") (M_check_solve_initialized + N_check_solve_initialized ) OIB )
  **  (simplex_pivot_memory S_check_solve_initialized M_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) ON OD )
  **  (simplex_solve_variables S_check_solve_initialized (M_check_solve_initialized + N_check_solve_initialized ) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_flags (N_check_solve_initialized) ((M_check_solve_initialized + N_check_solve_initialized ))) OVN OVD (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_zeroes ((M_check_solve_initialized + N_check_solve_initialized ))) (simplex_init_ones ((M_check_solve_initialized + N_check_solve_initialized ))) )))))
.

(* Shallow FunAssertion specs for sx_initialize. *)
Definition sx_initialize_sig : FuncSig := ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype.

Definition sx_initialize_check_init_matrix : Spec sx_initialize_sig :=
  fun F =>
ALL (A: (@list Z)),
ALL (M: Z),
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
ALL (Old: simplex_check_memory_snapshot),
ALL (CO: simplex_check_memory_snapshot),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (1 <= M) ”
  &&  “ (M <= 16) ”
  &&  “ (0 <= N) ”
  &&  “ (N <= 8) ”
  &&  “ ((Zlength (A)) = (M * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A ) ”
  &&  (simplex_check_old S M N Old )
  **  (simplex_check_frame S M N Old )
  **  (simplex_init_input C A M N )
  **  (simplex_check_input_frame C M N CO )))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 1 ) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (M + N ))
  **  (simplex_init_vars S N (M + N ) M (M + N ) (simplex_init_rhs (A) (M)) 1 )
  **  (simplex_init_rows S A N M M (M + N ) )
  **  (simplex_check_frame S M N Old )
  **  (simplex_init_input C A M N )
  **  (simplex_check_input_frame C M N CO )))
  F.

Definition sx_initialize_check_init_zero : Spec sx_initialize_sig :=
  fun F =>
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
ALL (Old: simplex_check_memory_snapshot),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (0 <= N) ”
  &&  “ (N <= 8) ”
  &&  (simplex_check_old S 0 N Old )
  **  (simplex_check_frame S 0 N Old )))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 1 ) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N ))
  **  (simplex_init_vars S N (0 + N ) 0 (0 + N ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S (@nil Z) N 0 0 (0 + N ) )
  **  (simplex_check_frame S 0 N Old )))
  F.

Definition sx_initialize_check_init_invalid : Spec sx_initialize_sig :=
  fun F =>
ALL (M: Z),
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (simplex_check_invalid_dimensions M N ) ”
  &&  emp))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 0 ) ”
  &&  emp))
  F.

Definition sx_initialize_invalid_dimensions : Spec sx_initialize_sig :=
  fun F =>
ALL (A: (@list Z)),
ALL (M: Z),
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
(orp
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (rows_pre < 0) ”
  &&  emp)
(orp
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (rows_pre > 16) ”
  &&  emp)
(orp
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (inputs_pre < 0) ”
  &&  emp)
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (inputs_pre > 8) ”
  &&  emp)))))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 0 ) ”
  &&  emp))
  F.

Definition sx_initialize_rejected_coefficient : Spec sx_initialize_sig :=
  fun F =>
ALL (A: (@list Z)),
ALL (M: Z),
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
  (EX (y: Z) (x: Z),
  “ (s_pre = S) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (c_pre = C) ”
  &&  “ (0 <= M) ”
  &&  “ (M <= 16) ”
  &&  “ (0 <= N) ”
  &&  “ (N <= 8) ”
  &&  “ ((Zlength (A)) = (M * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A) (0)) = (INT_MIN)) ”
  &&  (simplex_init_input C A M N )))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 0 ) ”
  &&  (simplex_init_input C A M N )))
  F.

Definition sx_initialize_initialized_matrix_non_alias : Spec sx_initialize_sig :=
  fun F =>
ALL (A: (@list Z)),
ALL (M: Z),
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
  (“ (s_pre = S) ”
  &&  “ (c_pre = C) ”
  &&  “ (rows_pre = M) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (1 <= M) ”
  &&  “ (M <= 16) ”
  &&  “ (0 <= N) ”
  &&  “ (N <= 8) ”
  &&  “ ((Zlength (A)) = (M * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A ) ”
  &&  (simplex_init_input C A M N )
  **  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S N 0 0 (M + N ) A 0 )
  **  (simplex_init_rows S A N 0 M (M + N ) )))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 1 ) ”
  &&  (simplex_init_input C A M N )
  **  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> M)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (M + N ))
  **  (simplex_init_vars S N (M + N ) M (M + N ) (simplex_init_rhs (A) (M)) 1 )
  **  (simplex_init_rows S A N M M (M + N ) )))
  F.

Definition sx_initialize_zero_rows : Spec sx_initialize_sig :=
  fun F =>
ALL (N: Z),
ALL (S: Z),
ALL (C: Z),
HoareFun ([ * struct "SxState"; i32; i32;  * i32.[9]], i32)%ctype
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) =>
  (“ (c_pre = C) ”
  &&  “ (s_pre = S) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N) ”
  &&  “ (0 <= N) ”
  &&  “ (N <= 8) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S N 0 0 (0 + N ) (@nil Z) 0 )
  **  (simplex_init_rows S (@nil Z) N 0 0 (0 + N ) )))
  (fun '(s_pre, (rows_pre, (inputs_pre, c_pre))) retval =>
  (“ (simplex_init_return retval 1 ) ”
  &&  ((&((S)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S)  # "SxState" ->ₛ "inputs")) # Int  |-> N)
  **  ((&((S)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N ))
  **  (simplex_init_vars S N (0 + N ) 0 (0 + N ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S (@nil Z) N 0 0 (0 + N ) )))
  F.

Definition sx_initialize_initialized_matrix_non_alias_entail_check_init_matrix :=
forall (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (A_check_init_matrix: (@list Z)) (M_check_init_matrix: Z) (N_check_init_matrix: Z) (S_check_init_matrix: Z) (C_check_init_matrix: Z) (Old_check_init_matrix: simplex_check_memory_snapshot) (CO_check_init_matrix: simplex_check_memory_snapshot),
  (“ (s_pre = S_check_init_matrix) ”
  &&  “ (c_pre = C_check_init_matrix) ”
  &&  “ (rows_pre = M_check_init_matrix) ”
  &&  “ (inputs_pre = N_check_init_matrix) ”
  &&  “ (1 <= M_check_init_matrix) ”
  &&  “ (M_check_init_matrix <= 16) ”
  &&  “ (0 <= N_check_init_matrix) ”
  &&  “ (N_check_init_matrix <= 8) ”
  &&  “ ((Zlength (A_check_init_matrix)) = (M_check_init_matrix * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_check_init_matrix ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_check_init_matrix ) ”
  &&  (simplex_check_old S_check_init_matrix M_check_init_matrix N_check_init_matrix Old_check_init_matrix )
  **  (simplex_check_frame S_check_init_matrix M_check_init_matrix N_check_init_matrix Old_check_init_matrix )
  **  (simplex_init_input C_check_init_matrix A_check_init_matrix M_check_init_matrix N_check_init_matrix )
  **  (simplex_check_input_frame C_check_init_matrix M_check_init_matrix N_check_init_matrix CO_check_init_matrix ))
|--
EX (A_initialized_matrix_non_alias: (@list Z))(M_initialized_matrix_non_alias: Z)(N_initialized_matrix_non_alias: Z)(S_initialized_matrix_non_alias: Z)(C_initialized_matrix_non_alias: Z),
  (“ (s_pre = S_initialized_matrix_non_alias) ”
  &&  “ (c_pre = C_initialized_matrix_non_alias) ”
  &&  “ (rows_pre = M_initialized_matrix_non_alias) ”
  &&  “ (inputs_pre = N_initialized_matrix_non_alias) ”
  &&  “ (1 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) ))
  **
  (ALL (retval: Z),
  (“ (simplex_init_return retval 1 ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) ))
  -*
  (“ (simplex_init_return retval 1 ) ”
  &&  ((&((S_check_init_matrix)  # "SxState" ->ₛ "rows")) # Int  |-> M_check_init_matrix)
  **  ((&((S_check_init_matrix)  # "SxState" ->ₛ "inputs")) # Int  |-> N_check_init_matrix)
  **  ((&((S_check_init_matrix)  # "SxState" ->ₛ "vars")) # Int  |-> (M_check_init_matrix + N_check_init_matrix ))
  **  (simplex_init_vars S_check_init_matrix N_check_init_matrix (M_check_init_matrix + N_check_init_matrix ) M_check_init_matrix (M_check_init_matrix + N_check_init_matrix ) (simplex_init_rhs (A_check_init_matrix) (M_check_init_matrix)) 1 )
  **  (simplex_init_rows S_check_init_matrix A_check_init_matrix N_check_init_matrix M_check_init_matrix M_check_init_matrix (M_check_init_matrix + N_check_init_matrix ) )
  **  (simplex_check_frame S_check_init_matrix M_check_init_matrix N_check_init_matrix Old_check_init_matrix )
  **  (simplex_init_input C_check_init_matrix A_check_init_matrix M_check_init_matrix N_check_init_matrix )
  **  (simplex_check_input_frame C_check_init_matrix M_check_init_matrix N_check_init_matrix CO_check_init_matrix )))
.

Definition sx_initialize_zero_rows_entail_check_init_zero :=
forall (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (N_check_init_zero: Z) (S_check_init_zero: Z) (C_check_init_zero: Z) (Old_check_init_zero: simplex_check_memory_snapshot),
  (“ (s_pre = S_check_init_zero) ”
  &&  “ (c_pre = C_check_init_zero) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N_check_init_zero) ”
  &&  “ (0 <= N_check_init_zero) ”
  &&  “ (N_check_init_zero <= 8) ”
  &&  (simplex_check_old S_check_init_zero 0 N_check_init_zero Old_check_init_zero )
  **  (simplex_check_frame S_check_init_zero 0 N_check_init_zero Old_check_init_zero ))
|--
EX (N_zero_rows: Z)(S_zero_rows: Z)(C_zero_rows: Z),
  (“ (c_pre = C_zero_rows) ”
  &&  “ (s_pre = S_zero_rows) ”
  &&  “ (rows_pre = 0) ”
  &&  “ (inputs_pre = N_zero_rows) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) nil 0 )
  **  (simplex_init_rows S_zero_rows nil N_zero_rows 0 0 (0 + N_zero_rows ) ))
  **
  (ALL (retval: Z),
  (“ (simplex_init_return retval 1 ) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (simplex_init_rhs (nil) (0)) 1 )
  **  (simplex_init_rows S_zero_rows nil N_zero_rows 0 0 (0 + N_zero_rows ) ))
  -*
  (“ (simplex_init_return retval 1 ) ”
  &&  ((&((S_check_init_zero)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_check_init_zero)  # "SxState" ->ₛ "inputs")) # Int  |-> N_check_init_zero)
  **  ((&((S_check_init_zero)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_check_init_zero ))
  **  (simplex_init_vars S_check_init_zero N_check_init_zero (0 + N_check_init_zero ) 0 (0 + N_check_init_zero ) (simplex_init_rhs (nil) (0)) 1 )
  **  (simplex_init_rows S_check_init_zero nil N_check_init_zero 0 0 (0 + N_check_init_zero ) )
  **  (simplex_check_frame S_check_init_zero 0 N_check_init_zero Old_check_init_zero )))
.

Definition sx_initialize_invalid_dimensions_entail_check_init_invalid :=
forall (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (M_check_init_invalid: Z) (N_check_init_invalid: Z) (S_check_init_invalid: Z) (C_check_init_invalid: Z),
  (“ (s_pre = S_check_init_invalid) ”
  &&  “ (c_pre = C_check_init_invalid) ”
  &&  “ (rows_pre = M_check_init_invalid) ”
  &&  “ (inputs_pre = N_check_init_invalid) ”
  &&  “ (simplex_check_invalid_dimensions M_check_init_invalid N_check_init_invalid ) ”
  &&  emp)
|--
EX (A_invalid_dimensions: (@list Z))(M_invalid_dimensions: Z)(N_invalid_dimensions: Z)(S_invalid_dimensions: Z)(C_invalid_dimensions: Z),
(orp
  (“ (s_pre = S_invalid_dimensions) ”
  &&  “ (c_pre = C_invalid_dimensions) ”
  &&  “ (rows_pre = M_invalid_dimensions) ”
  &&  “ (inputs_pre = N_invalid_dimensions) ”
  &&  “ (rows_pre < 0) ”
  &&  emp)
(orp
  (“ (s_pre = S_invalid_dimensions) ”
  &&  “ (c_pre = C_invalid_dimensions) ”
  &&  “ (rows_pre = M_invalid_dimensions) ”
  &&  “ (inputs_pre = N_invalid_dimensions) ”
  &&  “ (rows_pre > 16) ”
  &&  emp)
(orp
  (“ (s_pre = S_invalid_dimensions) ”
  &&  “ (c_pre = C_invalid_dimensions) ”
  &&  “ (rows_pre = M_invalid_dimensions) ”
  &&  “ (inputs_pre = N_invalid_dimensions) ”
  &&  “ (inputs_pre < 0) ”
  &&  emp)
  (“ (s_pre = S_invalid_dimensions) ”
  &&  “ (c_pre = C_invalid_dimensions) ”
  &&  “ (rows_pre = M_invalid_dimensions) ”
  &&  “ (inputs_pre = N_invalid_dimensions) ”
  &&  “ (inputs_pre > 8) ”
  &&  emp))))
  **
  (ALL (retval: Z),
  (“ (simplex_init_return retval 0 ) ”
  &&  emp)
  -*
  (“ (simplex_init_return retval 0 ) ”
  &&  emp))
.

Module Type VC_Correct.


Axiom proof_of_sx_check_safety_wit_1_matrix_normal_budget : sx_check_safety_wit_1_matrix_normal_budget.
Axiom proof_of_sx_check_safety_wit_2_matrix_negative_budget : sx_check_safety_wit_2_matrix_negative_budget.
Axiom proof_of_sx_check_safety_wit_3_zero_normal_budget : sx_check_safety_wit_3_zero_normal_budget.
Axiom proof_of_sx_check_safety_wit_4_zero_negative_budget : sx_check_safety_wit_4_zero_negative_budget.
Axiom proof_of_sx_check_safety_wit_5_check_rejected_coefficient : sx_check_safety_wit_5_check_rejected_coefficient.
Axiom proof_of_sx_check_safety_wit_6_check_invalid_dimensions : sx_check_safety_wit_6_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_7_check_invalid_dimensions : sx_check_safety_wit_7_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_8_check_invalid_dimensions : sx_check_safety_wit_8_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_9_check_invalid_dimensions : sx_check_safety_wit_9_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_10_check_invalid_dimensions : sx_check_safety_wit_10_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_11_check_invalid_dimensions : sx_check_safety_wit_11_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_12_check_invalid_dimensions : sx_check_safety_wit_12_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_13_check_invalid_dimensions : sx_check_safety_wit_13_check_invalid_dimensions.
Axiom proof_of_sx_check_safety_wit_14_check_rejected_coefficient : sx_check_safety_wit_14_check_rejected_coefficient.
Axiom proof_of_sx_check_safety_wit_15_zero_negative_budget : sx_check_safety_wit_15_zero_negative_budget.
Axiom proof_of_sx_check_safety_wit_16_zero_normal_budget : sx_check_safety_wit_16_zero_normal_budget.
Axiom proof_of_sx_check_safety_wit_17_matrix_negative_budget : sx_check_safety_wit_17_matrix_negative_budget.
Axiom proof_of_sx_check_safety_wit_18_matrix_normal_budget : sx_check_safety_wit_18_matrix_normal_budget.
Axiom proof_of_sx_check_return_wit_1_check_invalid_dimensions : sx_check_return_wit_1_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_2_check_invalid_dimensions : sx_check_return_wit_2_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_3_check_invalid_dimensions : sx_check_return_wit_3_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_4_check_invalid_dimensions : sx_check_return_wit_4_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_5_check_rejected_coefficient : sx_check_return_wit_5_check_rejected_coefficient.
Axiom proof_of_sx_check_return_wit_6_zero_negative_budget : sx_check_return_wit_6_zero_negative_budget.
Axiom proof_of_sx_check_return_wit_7_zero_normal_budget : sx_check_return_wit_7_zero_normal_budget.
Axiom proof_of_sx_check_return_wit_8_zero_normal_budget : sx_check_return_wit_8_zero_normal_budget.
Axiom proof_of_sx_check_return_wit_9_zero_normal_budget : sx_check_return_wit_9_zero_normal_budget.
Axiom proof_of_sx_check_return_wit_10_matrix_negative_budget : sx_check_return_wit_10_matrix_negative_budget.
Axiom proof_of_sx_check_return_wit_11_matrix_normal_budget : sx_check_return_wit_11_matrix_normal_budget.
Axiom proof_of_sx_check_return_wit_12_matrix_normal_budget : sx_check_return_wit_12_matrix_normal_budget.
Axiom proof_of_sx_check_return_wit_13_matrix_normal_budget : sx_check_return_wit_13_matrix_normal_budget.
Axiom proof_of_sx_check_return_wit_14_check_invalid_dimensions : sx_check_return_wit_14_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_15_check_invalid_dimensions : sx_check_return_wit_15_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_16_check_invalid_dimensions : sx_check_return_wit_16_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_17_check_invalid_dimensions : sx_check_return_wit_17_check_invalid_dimensions.
Axiom proof_of_sx_check_return_wit_18_check_rejected_coefficient : sx_check_return_wit_18_check_rejected_coefficient.
Axiom proof_of_sx_check_return_wit_19_zero_negative_budget : sx_check_return_wit_19_zero_negative_budget.
Axiom proof_of_sx_check_return_wit_20_zero_normal_budget : sx_check_return_wit_20_zero_normal_budget.
Axiom proof_of_sx_check_return_wit_21_matrix_negative_budget : sx_check_return_wit_21_matrix_negative_budget.
Axiom proof_of_sx_check_return_wit_22_matrix_normal_budget : sx_check_return_wit_22_matrix_normal_budget.
Axiom proof_of_sx_check_partial_solve_wit_1_check_invalid_dimensions_pure : sx_check_partial_solve_wit_1_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_1_check_invalid_dimensions : sx_check_partial_solve_wit_1_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_2_check_invalid_dimensions_pure : sx_check_partial_solve_wit_2_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_2_check_invalid_dimensions : sx_check_partial_solve_wit_2_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_3_check_invalid_dimensions_pure : sx_check_partial_solve_wit_3_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_3_check_invalid_dimensions : sx_check_partial_solve_wit_3_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_4_check_invalid_dimensions_pure : sx_check_partial_solve_wit_4_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_4_check_invalid_dimensions : sx_check_partial_solve_wit_4_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_5_check_rejected_coefficient_pure : sx_check_partial_solve_wit_5_check_rejected_coefficient_pure.
Axiom proof_of_sx_check_partial_solve_wit_5_check_rejected_coefficient : sx_check_partial_solve_wit_5_check_rejected_coefficient.
Axiom proof_of_sx_check_partial_solve_wit_6_zero_negative_budget_pure : sx_check_partial_solve_wit_6_zero_negative_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_6_zero_negative_budget : sx_check_partial_solve_wit_6_zero_negative_budget.
Axiom proof_of_sx_check_partial_solve_wit_7_zero_normal_budget_pure : sx_check_partial_solve_wit_7_zero_normal_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_7_zero_normal_budget : sx_check_partial_solve_wit_7_zero_normal_budget.
Axiom proof_of_sx_check_partial_solve_wit_8_matrix_negative_budget_pure : sx_check_partial_solve_wit_8_matrix_negative_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_8_matrix_negative_budget : sx_check_partial_solve_wit_8_matrix_negative_budget.
Axiom proof_of_sx_check_partial_solve_wit_9_matrix_normal_budget_pure : sx_check_partial_solve_wit_9_matrix_normal_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_9_matrix_normal_budget : sx_check_partial_solve_wit_9_matrix_normal_budget.
Axiom proof_of_sx_check_partial_solve_wit_10_check_invalid_dimensions_pure : sx_check_partial_solve_wit_10_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_10_check_invalid_dimensions : sx_check_partial_solve_wit_10_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_11_check_invalid_dimensions_pure : sx_check_partial_solve_wit_11_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_11_check_invalid_dimensions : sx_check_partial_solve_wit_11_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_12_check_invalid_dimensions_pure : sx_check_partial_solve_wit_12_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_12_check_invalid_dimensions : sx_check_partial_solve_wit_12_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_13_check_invalid_dimensions_pure : sx_check_partial_solve_wit_13_check_invalid_dimensions_pure.
Axiom proof_of_sx_check_partial_solve_wit_13_check_invalid_dimensions : sx_check_partial_solve_wit_13_check_invalid_dimensions.
Axiom proof_of_sx_check_partial_solve_wit_14_check_rejected_coefficient_pure : sx_check_partial_solve_wit_14_check_rejected_coefficient_pure.
Axiom proof_of_sx_check_partial_solve_wit_14_check_rejected_coefficient : sx_check_partial_solve_wit_14_check_rejected_coefficient.
Axiom proof_of_sx_check_partial_solve_wit_15_zero_negative_budget_pure : sx_check_partial_solve_wit_15_zero_negative_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_15_zero_negative_budget : sx_check_partial_solve_wit_15_zero_negative_budget.
Axiom proof_of_sx_check_partial_solve_wit_16_zero_normal_budget_pure : sx_check_partial_solve_wit_16_zero_normal_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_16_zero_normal_budget : sx_check_partial_solve_wit_16_zero_normal_budget.
Axiom proof_of_sx_check_partial_solve_wit_17_matrix_negative_budget_pure : sx_check_partial_solve_wit_17_matrix_negative_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_17_matrix_negative_budget : sx_check_partial_solve_wit_17_matrix_negative_budget.
Axiom proof_of_sx_check_partial_solve_wit_18_matrix_normal_budget_pure : sx_check_partial_solve_wit_18_matrix_normal_budget_pure.
Axiom proof_of_sx_check_partial_solve_wit_18_matrix_normal_budget : sx_check_partial_solve_wit_18_matrix_normal_budget.
Axiom proof_of_sx_solve_normal_state_entail_check_solve_initialized : sx_solve_normal_state_entail_check_solve_initialized.
Axiom proof_of_sx_initialize_initialized_matrix_non_alias_entail_check_init_matrix : sx_initialize_initialized_matrix_non_alias_entail_check_init_matrix.
Axiom proof_of_sx_initialize_zero_rows_entail_check_init_zero : sx_initialize_zero_rows_entail_check_init_zero.
Axiom proof_of_sx_initialize_invalid_dimensions_entail_check_init_invalid : sx_initialize_invalid_dimensions_entail_check_init_invalid.

End VC_Correct.
