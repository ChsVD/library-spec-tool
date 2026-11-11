From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.simplex_rat_zero.simplex_rat_zero_lib.
Require Import SimpleC.EE.Applications_human.simplex_recompute.simplex_recompute_lib.
Require Import SimpleC.EE.Applications_human.simplex_initialize.simplex_initialize_lib.
Local Open Scope sac.

(*----- Function sx_initialize -----*)

Definition sx_initialize_safety_wit_1_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (s_pre = S_invalid_dimensions)) (PreH2 : (c_pre = C_invalid_dimensions)) (PreH3 : (rows_pre = M_invalid_dimensions)) (PreH4 : (inputs_pre = N_invalid_dimensions)) (PreH5 : (rows_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_2_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (s_pre = S_invalid_dimensions)) (PreH2 : (c_pre = C_invalid_dimensions)) (PreH3 : (rows_pre = M_invalid_dimensions)) (PreH4 : (inputs_pre = N_invalid_dimensions)) (PreH5 : (rows_pre > 16)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_3_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (s_pre = S_invalid_dimensions)) (PreH2 : (c_pre = C_invalid_dimensions)) (PreH3 : (rows_pre = M_invalid_dimensions)) (PreH4 : (inputs_pre = N_invalid_dimensions)) (PreH5 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_4_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (s_pre = S_invalid_dimensions)) (PreH2 : (c_pre = C_invalid_dimensions)) (PreH3 : (rows_pre = M_invalid_dimensions)) (PreH4 : (inputs_pre = N_invalid_dimensions)) (PreH5 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_5_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (s_pre = S_rejected_coefficient)) (PreH2 : (rows_pre = M_rejected_coefficient)) (PreH3 : (inputs_pre = N_rejected_coefficient)) (PreH4 : (c_pre = C_rejected_coefficient)) (PreH5 : (0 <= M_rejected_coefficient)) (PreH6 : (M_rejected_coefficient <= 16)) (PreH7 : (0 <= N_rejected_coefficient)) (PreH8 : (N_rejected_coefficient <= 8)) (PreH9 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH10 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH12 : (0 <= x)) (PreH13 : (x < M_rejected_coefficient)) (PreH14 : (0 <= y)) (PreH15 : (y <= N_rejected_coefficient)) (PreH16 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_6_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (s_pre = S_initialized_matrix_non_alias)) (PreH2 : (c_pre = C_initialized_matrix_non_alias)) (PreH3 : (rows_pre = M_initialized_matrix_non_alias)) (PreH4 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH5 : (1 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_7_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (c_pre = C_zero_rows)) (PreH2 : (s_pre = S_zero_rows)) (PreH3 : (rows_pre = 0)) (PreH4 : (inputs_pre = N_zero_rows)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_8_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_9_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre > 16)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_10_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_rejected_coefficient)) (PreH3 : (rows_pre = M_rejected_coefficient)) (PreH4 : (inputs_pre = N_rejected_coefficient)) (PreH5 : (c_pre = C_rejected_coefficient)) (PreH6 : (0 <= M_rejected_coefficient)) (PreH7 : (M_rejected_coefficient <= 16)) (PreH8 : (0 <= N_rejected_coefficient)) (PreH9 : (N_rejected_coefficient <= 8)) (PreH10 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH11 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH13 : (0 <= x)) (PreH14 : (x < M_rejected_coefficient)) (PreH15 : (0 <= y)) (PreH16 : (y <= N_rejected_coefficient)) (PreH17 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_11_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_initialized_matrix_non_alias)) (PreH3 : (c_pre = C_initialized_matrix_non_alias)) (PreH4 : (rows_pre = M_initialized_matrix_non_alias)) (PreH5 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH6 : (1 <= M_initialized_matrix_non_alias)) (PreH7 : (M_initialized_matrix_non_alias <= 16)) (PreH8 : (0 <= N_initialized_matrix_non_alias)) (PreH9 : (N_initialized_matrix_non_alias <= 8)) (PreH10 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_12_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (c_pre = C_zero_rows)) (PreH3 : (s_pre = S_zero_rows)) (PreH4 : (rows_pre = 0)) (PreH5 : (inputs_pre = N_zero_rows)) (PreH6 : (0 <= N_zero_rows)) (PreH7 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_13_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (c_pre = C_zero_rows)) (PreH3 : (s_pre = S_zero_rows)) (PreH4 : (rows_pre = 0)) (PreH5 : (inputs_pre = N_zero_rows)) (PreH6 : (0 <= N_zero_rows)) (PreH7 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition sx_initialize_safety_wit_14_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (s_pre = S_initialized_matrix_non_alias)) (PreH3 : (c_pre = C_initialized_matrix_non_alias)) (PreH4 : (rows_pre = M_initialized_matrix_non_alias)) (PreH5 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH6 : (1 <= M_initialized_matrix_non_alias)) (PreH7 : (M_initialized_matrix_non_alias <= 16)) (PreH8 : (0 <= N_initialized_matrix_non_alias)) (PreH9 : (N_initialized_matrix_non_alias <= 8)) (PreH10 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition sx_initialize_safety_wit_15_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (s_pre = S_rejected_coefficient)) (PreH3 : (rows_pre = M_rejected_coefficient)) (PreH4 : (inputs_pre = N_rejected_coefficient)) (PreH5 : (c_pre = C_rejected_coefficient)) (PreH6 : (0 <= M_rejected_coefficient)) (PreH7 : (M_rejected_coefficient <= 16)) (PreH8 : (0 <= N_rejected_coefficient)) (PreH9 : (N_rejected_coefficient <= 8)) (PreH10 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH11 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH13 : (0 <= x)) (PreH14 : (x < M_rejected_coefficient)) (PreH15 : (0 <= y)) (PreH16 : (y <= N_rejected_coefficient)) (PreH17 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition sx_initialize_safety_wit_16_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition sx_initialize_safety_wit_17_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition sx_initialize_safety_wit_18_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre >= 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre > 16)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (16 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 16) ”
.

Definition sx_initialize_safety_wit_19_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (c_pre = C_zero_rows)) (PreH4 : (s_pre = S_zero_rows)) (PreH5 : (rows_pre = 0)) (PreH6 : (inputs_pre = N_zero_rows)) (PreH7 : (0 <= N_zero_rows)) (PreH8 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_20_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_initialized_matrix_non_alias)) (PreH4 : (c_pre = C_initialized_matrix_non_alias)) (PreH5 : (rows_pre = M_initialized_matrix_non_alias)) (PreH6 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH7 : (1 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_21_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_rejected_coefficient)) (PreH4 : (rows_pre = M_rejected_coefficient)) (PreH5 : (inputs_pre = N_rejected_coefficient)) (PreH6 : (c_pre = C_rejected_coefficient)) (PreH7 : (0 <= M_rejected_coefficient)) (PreH8 : (M_rejected_coefficient <= 16)) (PreH9 : (0 <= N_rejected_coefficient)) (PreH10 : (N_rejected_coefficient <= 8)) (PreH11 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH12 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH14 : (0 <= x)) (PreH15 : (x < M_rejected_coefficient)) (PreH16 : (0 <= y)) (PreH17 : (y <= N_rejected_coefficient)) (PreH18 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_22_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre <= 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (rows_pre > 16)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_23_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre <= 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (c_pre = C_zero_rows)) (PreH4 : (s_pre = S_zero_rows)) (PreH5 : (rows_pre = 0)) (PreH6 : (inputs_pre = N_zero_rows)) (PreH7 : (0 <= N_zero_rows)) (PreH8 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_24_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre <= 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_initialized_matrix_non_alias)) (PreH4 : (c_pre = C_initialized_matrix_non_alias)) (PreH5 : (rows_pre = M_initialized_matrix_non_alias)) (PreH6 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH7 : (1 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_25_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre <= 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_rejected_coefficient)) (PreH4 : (rows_pre = M_rejected_coefficient)) (PreH5 : (inputs_pre = N_rejected_coefficient)) (PreH6 : (c_pre = C_rejected_coefficient)) (PreH7 : (0 <= M_rejected_coefficient)) (PreH8 : (M_rejected_coefficient <= 16)) (PreH9 : (0 <= N_rejected_coefficient)) (PreH10 : (N_rejected_coefficient <= 8)) (PreH11 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH12 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH14 : (0 <= x)) (PreH15 : (x < M_rejected_coefficient)) (PreH16 : (0 <= y)) (PreH17 : (y <= N_rejected_coefficient)) (PreH18 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_26_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre <= 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_27_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre <= 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_28_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (c_pre = C_zero_rows)) (PreH5 : (s_pre = S_zero_rows)) (PreH6 : (rows_pre = 0)) (PreH7 : (inputs_pre = N_zero_rows)) (PreH8 : (0 <= N_zero_rows)) (PreH9 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_29_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_initialized_matrix_non_alias)) (PreH5 : (c_pre = C_initialized_matrix_non_alias)) (PreH6 : (rows_pre = M_initialized_matrix_non_alias)) (PreH7 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH8 : (1 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_30_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_rejected_coefficient)) (PreH5 : (rows_pre = M_rejected_coefficient)) (PreH6 : (inputs_pre = N_rejected_coefficient)) (PreH7 : (c_pre = C_rejected_coefficient)) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_31_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_32_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre >= 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_33_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre >= 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (c_pre = C_zero_rows)) (PreH5 : (s_pre = S_zero_rows)) (PreH6 : (rows_pre = 0)) (PreH7 : (inputs_pre = N_zero_rows)) (PreH8 : (0 <= N_zero_rows)) (PreH9 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sx_initialize_safety_wit_34_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre >= 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_initialized_matrix_non_alias)) (PreH5 : (c_pre = C_initialized_matrix_non_alias)) (PreH6 : (rows_pre = M_initialized_matrix_non_alias)) (PreH7 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH8 : (1 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sx_initialize_safety_wit_35_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre >= 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_rejected_coefficient)) (PreH5 : (rows_pre = M_rejected_coefficient)) (PreH6 : (inputs_pre = N_rejected_coefficient)) (PreH7 : (c_pre = C_rejected_coefficient)) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (0 <= x)) (PreH16 : (x < M_rejected_coefficient)) (PreH17 : (0 <= y)) (PreH18 : (y <= N_rejected_coefficient)) (PreH19 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sx_initialize_safety_wit_36_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre >= 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (8 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 8) ”
.

Definition sx_initialize_safety_wit_37_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (c_pre = C_zero_rows)) (PreH6 : (s_pre = S_zero_rows)) (PreH7 : (rows_pre = 0)) (PreH8 : (inputs_pre = N_zero_rows)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_38_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_initialized_matrix_non_alias)) (PreH6 : (c_pre = C_initialized_matrix_non_alias)) (PreH7 : (rows_pre = M_initialized_matrix_non_alias)) (PreH8 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH9 : (1 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_39_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_rejected_coefficient)) (PreH6 : (rows_pre = M_rejected_coefficient)) (PreH7 : (inputs_pre = N_rejected_coefficient)) (PreH8 : (c_pre = C_rejected_coefficient)) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (0 <= x)) (PreH17 : (x < M_rejected_coefficient)) (PreH18 : (0 <= y)) (PreH19 : (y <= N_rejected_coefficient)) (PreH20 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ False ”
.

Definition sx_initialize_safety_wit_40_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_invalid_dimensions)) (PreH6 : (c_pre = C_invalid_dimensions)) (PreH7 : (rows_pre = M_invalid_dimensions)) (PreH8 : (inputs_pre = N_invalid_dimensions)) (PreH9 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_41_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_42_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_43_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_44_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_45_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (rows_pre > 16)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_46_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre < 0)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_47_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_48_invalid_dimensions :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_invalid_dimensions)) (PreH6 : (c_pre = C_invalid_dimensions)) (PreH7 : (rows_pre = M_invalid_dimensions)) (PreH8 : (inputs_pre = N_invalid_dimensions)) (PreH9 : (inputs_pre > 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_49_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_rejected_coefficient)) (PreH6 : (rows_pre = M_rejected_coefficient)) (PreH7 : (inputs_pre = N_rejected_coefficient)) (PreH8 : (c_pre = C_rejected_coefficient)) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (0 <= x)) (PreH17 : (x < M_rejected_coefficient)) (PreH18 : (0 <= y)) (PreH19 : (y <= N_rejected_coefficient)) (PreH20 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_50_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_initialized_matrix_non_alias)) (PreH6 : (c_pre = C_initialized_matrix_non_alias)) (PreH7 : (rows_pre = M_initialized_matrix_non_alias)) (PreH8 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH9 : (1 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_51_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (c_pre = C_zero_rows)) (PreH6 : (s_pre = S_zero_rows)) (PreH7 : (rows_pre = 0)) (PreH8 : (inputs_pre = N_zero_rows)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)),
  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_52_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i < rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)) (PreH9 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN)))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_53_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (y_2: Z) (x_2: Z) (PreH1 : (i < M_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_2)) (PreH10 : (x_2 < M_rejected_coefficient)) (PreH11 : (0 <= y_2)) (PreH12 : (y_2 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_rejected_coefficient)) /\ (0 <= y)) /\ (y <= N_rejected_coefficient)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_54_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_55_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : (j <= N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x)) (PreH10 : (x < M_rejected_coefficient)) (PreH11 : (0 <= y)) (PreH12 : (y <= N_rejected_coefficient)) (PreH13 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition sx_initialize_safety_wit_56_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (((-INT_MAX) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((-INT_MAX) - 1 )) ”
.

Definition sx_initialize_safety_wit_57_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : (j <= N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x)) (PreH10 : (x < M_rejected_coefficient)) (PreH11 : (0 <= y)) (PreH12 : (y <= N_rejected_coefficient)) (PreH13 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition sx_initialize_safety_wit_58_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (INT_MAX <> (INT_MIN)) ”
.

Definition sx_initialize_safety_wit_59_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ”
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition sx_initialize_safety_wit_60_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : (j <= N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x)) (PreH10 : (x < M_rejected_coefficient)) (PreH11 : (0 <= y)) (PreH12 : (y <= N_rejected_coefficient)) (PreH13 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (INT_MAX <= INT_MAX) ”
  &&  “ ((INT_MIN) <= INT_MAX) ”
.

Definition sx_initialize_safety_wit_61_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_62_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : (j <= N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x)) (PreH10 : (x < M_rejected_coefficient)) (PreH11 : (0 <= y)) (PreH12 : (y <= N_rejected_coefficient)) (PreH13 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_63_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) = ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)) (PreH12 : (i < M_initialized_matrix_non_alias)) (PreH13 : (0 <= j)) (PreH14 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH15 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_64_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) = ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_rejected_coefficient)) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= x)) (PreH11 : (x < M_rejected_coefficient)) (PreH12 : (0 <= y)) (PreH13 : (y <= N_rejected_coefficient)) (PreH14 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH15 : (0 <= i)) (PreH16 : (i <= M_rejected_coefficient)) (PreH17 : (i < M_rejected_coefficient)) (PreH18 : (0 <= j)) (PreH19 : (j <= (N_rejected_coefficient + 1 ))) (PreH20 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_65_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (y_2: Z) (x_2: Z) (PreH1 : (j > N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_2)) (PreH10 : (x_2 < M_rejected_coefficient)) (PreH11 : (0 <= y_2)) (PreH12 : (y_2 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_rejected_coefficient)) /\ (0 <= y)) /\ (y <= N_rejected_coefficient)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sx_initialize_safety_wit_66_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sx_initialize_safety_wit_67_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <> ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)) (PreH12 : (i < M_initialized_matrix_non_alias)) (PreH13 : (0 <= j)) (PreH14 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH15 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_68_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <> ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_rejected_coefficient)) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= x)) (PreH11 : (x < M_rejected_coefficient)) (PreH12 : (0 <= y)) (PreH13 : (y <= N_rejected_coefficient)) (PreH14 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH15 : (0 <= i)) (PreH16 : (i <= M_rejected_coefficient)) (PreH17 : (i < M_rejected_coefficient)) (PreH18 : (0 <= j)) (PreH19 : (j <= (N_rejected_coefficient + 1 ))) (PreH20 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_69_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient 0 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((M_rejected_coefficient + N_rejected_coefficient ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (M_rejected_coefficient + N_rejected_coefficient )) ”
.

Definition sx_initialize_safety_wit_70_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
.

Definition sx_initialize_safety_wit_71_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i >= rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)) (PreH9 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN)))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ ((rows + N_zero_rows ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (rows + N_zero_rows )) ”
.

Definition sx_initialize_safety_wit_72_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient 0 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_73_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_74_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i >= rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)) (PreH9 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN)))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (rows + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_75_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_76_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_77_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_78_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_79_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_80_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_81_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_82_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_83_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_84_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_85_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_86_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_87_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j >= (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_88_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_89_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_90_zero_rows :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i < rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ False ”
.

Definition sx_initialize_safety_wit_91_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((N_initialized_matrix_non_alias + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (N_initialized_matrix_non_alias + i )) ”
.

Definition sx_initialize_safety_wit_92_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i < M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ ((N_rejected_coefficient + i ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (N_rejected_coefficient + i )) ”
.

Definition sx_initialize_safety_wit_93_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (b = (N_initialized_matrix_non_alias + i ))) (PreH2 : (i < M_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_94_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (b = (N_rejected_coefficient + i ))) (PreH3 : (i < M_rejected_coefficient)) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i <= M_rejected_coefficient)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_95_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (b = (N_initialized_matrix_non_alias + i ))) (PreH2 : (i < M_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_96_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (b = (N_rejected_coefficient + i ))) (PreH3 : (i < M_rejected_coefficient)) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i <= M_rejected_coefficient)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_97_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (b = (N_initialized_matrix_non_alias + i ))) (PreH2 : (i < M_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_98_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (b = (N_rejected_coefficient + i ))) (PreH3 : (i < M_rejected_coefficient)) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i <= M_rejected_coefficient)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_99_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (b = (N_initialized_matrix_non_alias + i ))) (PreH2 : (i < M_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_100_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (b = (N_rejected_coefficient + i ))) (PreH3 : (i < M_rejected_coefficient)) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i <= M_rejected_coefficient)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_101_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (b = (N_initialized_matrix_non_alias + i ))) (PreH2 : (i < M_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_102_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (b = (N_rejected_coefficient + i ))) (PreH3 : (i < M_rejected_coefficient)) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i <= M_rejected_coefficient)),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_initialize_safety_wit_103_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < N_rejected_coefficient)) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_104_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < N_rejected_coefficient)) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_105_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_106_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_initialize_safety_wit_107_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < N_rejected_coefficient)) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_108_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_109_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j >= N_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_110_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j >= N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition sx_initialize_safety_wit_111_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i < M_rejected_coefficient)) (PreH12 : (b = (N_rejected_coefficient + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sx_initialize_safety_wit_112_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i < M_initialized_matrix_non_alias)) (PreH11 : (b = (N_initialized_matrix_non_alias + i ))) (PreH12 : (0 <= j)) (PreH13 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sx_initialize_entail_wit_1_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x_3: Z) (y_3: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_rejected_coefficient)) (PreH6 : (rows_pre = M_rejected_coefficient)) (PreH7 : (inputs_pre = N_rejected_coefficient)) (PreH8 : (c_pre = C_rejected_coefficient)) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (0 <= x_3)) (PreH17 : (x_3 < M_rejected_coefficient)) (PreH18 : (0 <= y_3)) (PreH19 : (y_3 <= N_rejected_coefficient)) (PreH20 : ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ (x_2 < 0)) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x_3: Z) (y_3: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_rejected_coefficient)) (PreH6 : (rows_pre = M_rejected_coefficient)) (PreH7 : (inputs_pre = N_rejected_coefficient)) (PreH8 : (c_pre = C_rejected_coefficient)) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (0 <= x_3)) (PreH17 : (x_3 < M_rejected_coefficient)) (PreH18 : (0 <= y_3)) (PreH19 : (y_3 <= N_rejected_coefficient)) (PreH20 : ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) = (INT_MIN))),
  TT && emp 
|--
  EX (y: Z) (x: Z),
  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= 0) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ (x_2 < 0)) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_2_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_initialized_matrix_non_alias)) (PreH6 : (c_pre = C_initialized_matrix_non_alias)) (PreH7 : (rows_pre = M_initialized_matrix_non_alias)) (PreH8 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH9 : (1 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "rows" ) )) # Int  |-> rows_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < 0)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_initialized_matrix_non_alias)) (PreH6 : (c_pre = C_initialized_matrix_non_alias)) (PreH7 : (rows_pre = M_initialized_matrix_non_alias)) (PreH8 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH9 : (1 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  TT && emp 
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < 0)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_2_initialized_matrix_non_alias_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_initialized_matrix_non_alias)) (PreH6 : (c_pre = C_initialized_matrix_non_alias)) (PreH7 : (rows_pre = M_initialized_matrix_non_alias)) (PreH8 : (inputs_pre = N_initialized_matrix_non_alias)) (PreH9 : (1 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )),
  forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < 0)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))
.

Definition sx_initialize_entail_wit_3_zero_rows :=
(
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (c_pre = C_zero_rows)) (PreH6 : (s_pre = S_zero_rows)) (PreH7 : (rows_pre = 0)) (PreH8 : (inputs_pre = N_zero_rows)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "inputs" ) )) # Int  |-> inputs_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (rows_pre = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < 0)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN))) ”
  &&  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
) \/
(
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (c_pre = C_zero_rows)) (PreH6 : (s_pre = S_zero_rows)) (PreH7 : (rows_pre = 0)) (PreH8 : (inputs_pre = N_zero_rows)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)),
  TT && emp 
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < 0)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_3_zero_rows_split_goal_1 :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre <= 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (c_pre = C_zero_rows)) (PreH6 : (s_pre = S_zero_rows)) (PreH7 : (rows_pre = 0)) (PreH8 : (inputs_pre = N_zero_rows)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)),
  forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < 0)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN)))
.

Definition sx_initialize_entail_wit_4_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (y_4: Z) (x_4: Z) (PreH1 : (i < M_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_4)) (PreH10 : (x_4 < M_rejected_coefficient)) (PreH11 : (0 <= y_4)) (PreH12 : (y_4 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : forall (x_3: Z), forall (y_3: Z), ((((((0 <= x_3) /\ (x_3 < M_rejected_coefficient)) /\ (0 <= y_3)) /\ (y_3 <= N_rejected_coefficient)) /\ (x_3 < i)) -> ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (N_rejected_coefficient + 1 )) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < 0)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
) \/
(
forall (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (y_4: Z) (x_4: Z) (PreH1 : (i < M_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_4)) (PreH10 : (x_4 < M_rejected_coefficient)) (PreH11 : (0 <= y_4)) (PreH12 : (y_4 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : forall (x_3: Z), forall (y_3: Z), ((((((0 <= x_3) /\ (x_3 < M_rejected_coefficient)) /\ (0 <= y_3)) /\ (y_3 <= N_rejected_coefficient)) /\ (x_3 < i)) -> ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  TT && emp 
|--
  EX (y: Z) (x: Z),
  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (N_rejected_coefficient + 1 )) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < 0)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_5_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ (x_2 < i)) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_initialized_matrix_non_alias) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (N_initialized_matrix_non_alias + 1 )) ”
  &&  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < 0)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ (x_2 < i)) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  TT && emp 
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < 0)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_5_initialized_matrix_non_alias_split_goal_1 :=
forall (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ (x_2 < i)) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < 0)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))
.

Definition sx_initialize_entail_wit_6_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (y_4: Z) (x_4: Z) (PreH1 : (j <= N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_4)) (PreH10 : (x_4 < M_rejected_coefficient)) (PreH11 : (0 <= y_4)) (PreH12 : (y_4 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_3: Z), forall (y_3: Z), ((((((0 <= x_3) /\ (x_3 < M_rejected_coefficient)) /\ (0 <= y_3)) /\ (y_3 <= N_rejected_coefficient)) /\ ((x_3 < i) \/ ((x_3 = i) /\ (y_3 < j)))) -> ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (j <= N_rejected_coefficient) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (N_rejected_coefficient + 1 )) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
) \/
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (y_4: Z) (x_4: Z) (PreH1 : (j <= N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_4)) (PreH10 : (x_4 < M_rejected_coefficient)) (PreH11 : (0 <= y_4)) (PreH12 : (y_4 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_3: Z), forall (y_3: Z), ((((((0 <= x_3) /\ (x_3 < M_rejected_coefficient)) /\ (0 <= y_3)) /\ (y_3 <= N_rejected_coefficient)) /\ ((x_3 < i) \/ ((x_3 = i) /\ (y_3 < j)))) -> ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (j <= N_rejected_coefficient) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (N_rejected_coefficient + 1 )) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
).

Definition sx_initialize_entail_wit_7_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (j <= N_initialized_matrix_non_alias) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_initialized_matrix_non_alias) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (N_initialized_matrix_non_alias + 1 )) ”
  &&  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
.

Definition sx_initialize_entail_wit_7_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j <= N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_8_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (y_2: Z) (x_2: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_2)) (PreH10 : (x_2 < M_rejected_coefficient)) (PreH11 : (0 <= y_2)) (PreH12 : (y_2 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_rejected_coefficient)) /\ (0 <= y)) /\ (y <= N_rejected_coefficient)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient 0 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (y_2: Z) (x_2: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_2)) (PreH10 : (x_2 < M_rejected_coefficient)) (PreH11 : (0 <= y_2)) (PreH12 : (y_2 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_rejected_coefficient)) /\ (0 <= y)) /\ (y <= N_rejected_coefficient)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  EX (x_5: Z) (x_4: Z) (x_3: Z),
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> x_5)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> x_4)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> x_3)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient 0 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_9_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (y_4: Z) (x_4: Z) (PreH1 : (j > N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_4)) (PreH10 : (x_4 < M_rejected_coefficient)) (PreH11 : (0 <= y_4)) (PreH12 : (y_4 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_3: Z), forall (y_3: Z), ((((((0 <= x_3) /\ (x_3 < M_rejected_coefficient)) /\ (0 <= y_3)) /\ (y_3 <= N_rejected_coefficient)) /\ ((x_3 < i) \/ ((x_3 = i) /\ (y_3 < j)))) -> ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
|--
  EX (y: Z) (x: Z),
  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= M_rejected_coefficient) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ (x_2 < (i + 1 ))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (y_4: Z) (x_4: Z) (PreH1 : (j > N_rejected_coefficient)) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (0 <= x_4)) (PreH10 : (x_4 < M_rejected_coefficient)) (PreH11 : (0 <= y_4)) (PreH12 : (y_4 <= N_rejected_coefficient)) (PreH13 : ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH14 : (0 <= i)) (PreH15 : (i <= M_rejected_coefficient)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (0 <= j)) (PreH18 : (j <= (N_rejected_coefficient + 1 ))) (PreH19 : forall (x_3: Z), forall (y_3: Z), ((((((0 <= x_3) /\ (x_3 < M_rejected_coefficient)) /\ (0 <= y_3)) /\ (y_3 <= N_rejected_coefficient)) /\ ((x_3 < i) \/ ((x_3 = i) /\ (y_3 < j)))) -> ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  TT && emp 
|--
  EX (y: Z) (x: Z),
  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= M_rejected_coefficient) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ (x_2 < (i + 1 ))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_10_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= M_initialized_matrix_non_alias) ”
  &&  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < (i + 1 ))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  TT && emp 
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < (i + 1 ))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  emp
).

Definition sx_initialize_entail_wit_10_initialized_matrix_non_alias_split_goal_1 :=
forall (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : (j > N_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (0 <= j)) (PreH13 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH14 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < (i + 1 ))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))
.

Definition sx_initialize_entail_wit_11_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <> ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)) (PreH12 : (i < M_initialized_matrix_non_alias)) (PreH13 : (0 <= j)) (PreH14 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH15 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_initialized_matrix_non_alias) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (N_initialized_matrix_non_alias + 1 )) ”
  &&  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < (j + 1 ))))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <> ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_initialized_matrix_non_alias)) (PreH5 : (0 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH12 : (0 <= i)) (PreH13 : (i <= M_initialized_matrix_non_alias)) (PreH14 : (i < M_initialized_matrix_non_alias)) (PreH15 : (0 <= j)) (PreH16 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH17 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < (j + 1 ))))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <> ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_initialized_matrix_non_alias)) (PreH5 : (0 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH12 : (0 <= i)) (PreH13 : (i <= M_initialized_matrix_non_alias)) (PreH14 : (i < M_initialized_matrix_non_alias)) (PreH15 : (0 <= j)) (PreH16 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH17 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < (j + 1 ))))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN))) ”
.

Definition sx_initialize_entail_wit_11_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <> ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_initialized_matrix_non_alias)) (PreH5 : (0 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH12 : (0 <= i)) (PreH13 : (i <= M_initialized_matrix_non_alias)) (PreH14 : (i < M_initialized_matrix_non_alias)) (PreH15 : (0 <= j)) (PreH16 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH17 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_initialized_matrix_non_alias)) /\ (0 <= y_2)) /\ (y_2 <= N_initialized_matrix_non_alias)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_12_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x_3: Z) (y_3: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <> ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_rejected_coefficient)) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= x_3)) (PreH11 : (x_3 < M_rejected_coefficient)) (PreH12 : (0 <= y_3)) (PreH13 : (y_3 <= N_rejected_coefficient)) (PreH14 : ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH15 : (0 <= i)) (PreH16 : (i <= M_rejected_coefficient)) (PreH17 : (i < M_rejected_coefficient)) (PreH18 : (0 <= j)) (PreH19 : (j <= (N_rejected_coefficient + 1 ))) (PreH20 : forall (x_4: Z), forall (y_4: Z), ((((((0 <= x_4) /\ (x_4 < M_rejected_coefficient)) /\ (0 <= y_4)) /\ (y_4 <= N_rejected_coefficient)) /\ ((x_4 < i) \/ ((x_4 = i) /\ (y_4 < j)))) -> ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
|--
  EX (y: Z) (x: Z),
  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (N_rejected_coefficient + 1 )) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < (j + 1 ))))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
) \/
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x_3: Z) (y_3: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <> ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_rejected_coefficient)) (PreH5 : (0 <= M_rejected_coefficient)) (PreH6 : (M_rejected_coefficient <= 16)) (PreH7 : (0 <= N_rejected_coefficient)) (PreH8 : (N_rejected_coefficient <= 8)) (PreH9 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH10 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH12 : (0 <= x_3)) (PreH13 : (x_3 < M_rejected_coefficient)) (PreH14 : (0 <= y_3)) (PreH15 : (y_3 <= N_rejected_coefficient)) (PreH16 : ((Znth (((x_3 * 9 ) + y_3 )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH17 : (0 <= i)) (PreH18 : (i <= M_rejected_coefficient)) (PreH19 : (i < M_rejected_coefficient)) (PreH20 : (0 <= j)) (PreH21 : (j <= (N_rejected_coefficient + 1 ))) (PreH22 : forall (x_4: Z), forall (y_4: Z), ((((((0 <= x_4) /\ (x_4 < M_rejected_coefficient)) /\ (0 <= y_4)) /\ (y_4 <= N_rejected_coefficient)) /\ ((x_4 < i) \/ ((x_4 = i) /\ (y_4 < j)))) -> ((Znth (((x_4 * 9 ) + y_4 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
|--
  EX (y: Z) (x: Z),
  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((INT_MIN))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= x) ”
  &&  “ (x < M_rejected_coefficient) ”
  &&  “ (0 <= y) ”
  &&  “ (y <= N_rejected_coefficient) ”
  &&  “ ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN)) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (N_rejected_coefficient + 1 )) ”
  &&  “ forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < (j + 1 ))))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN))) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
).

Definition sx_initialize_entail_wit_13_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient 0 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient 0 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  TT && emp 
|--
  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  emp
).

Definition sx_initialize_entail_wit_13_rejected_coefficient_split_goal_1 :=
forall (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )
.

Definition sx_initialize_entail_wit_13_rejected_coefficient_split_goal_2 :=
forall (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )
.

Definition sx_initialize_entail_wit_13_rejected_coefficient_split_goal_3 :=
forall (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)),
  ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))
.

Definition sx_initialize_entail_wit_14_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)) (PreH11 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
.

Definition sx_initialize_entail_wit_15_zero_rows :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i >= rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)) (PreH9 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < 0)) /\ (0 <= y)) /\ (y <= N_zero_rows)) /\ (x < i)) -> ((Znth (((x * 9 ) + y )) ((@nil Z)) (0)) <> (INT_MIN)))),
  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (rows + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (0 + N_zero_rows )) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows 0 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "i" ) )) # Int  |->_)
.

Definition sx_initialize_entail_wit_16_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  EX (x_9: Z) (x_8: Z) (x_7: Z) (x_6: Z) (x_5: Z) (x_4: Z) (x_3: Z) (x_2: Z) (x: Z),
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_9)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_8)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_7)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_6)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_5)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_4)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> x_3)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> x_2)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> x)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_17_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  EX (x_9: Z) (x_8: Z) (x_7: Z) (x_6: Z) (x_5: Z) (x_4: Z) (x_3: Z) (x_2: Z) (x: Z),
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_9)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_8)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_7)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_6)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_5)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_4)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> x_3)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> x_2)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> x)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_18_zero_rows :=
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (j < (0 + N_zero_rows )) ”
  &&  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (0 + N_zero_rows )) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |->_)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
) \/
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  (simplex_init_vars S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  EX (x_9: Z) (x_8: Z) (x_7: Z) (x_6: Z) (x_5: Z) (x_4: Z) (x_3: Z) (x_2: Z) (x: Z),
  “ (j < (0 + N_zero_rows )) ”
  &&  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (0 + N_zero_rows )) ”
  &&  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_9)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_8)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_7)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_6)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_5)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_4)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> x_3)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> x_2)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> x)
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
).

Definition sx_initialize_entail_wit_19_zero_rows :=
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (0 + N_zero_rows )) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (j + 1 ) 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
) \/
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j < (0 + N_zero_rows ))) (PreH6 : (rows = 0)) (PreH7 : (0 <= 0)) (PreH8 : (0 <= 16)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)) (PreH11 : (0 <= j)) (PreH12 : (j <= (0 + N_zero_rows ))),
  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  (simplex_init_vars S_zero_rows N_zero_rows (j + 1 ) 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
).

Definition sx_initialize_entail_wit_19_zero_rows_split_goal_spatial :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j < (0 + N_zero_rows ))) (PreH6 : (rows = 0)) (PreH7 : (0 <= 0)) (PreH8 : (0 <= 16)) (PreH9 : (0 <= N_zero_rows)) (PreH10 : (N_zero_rows <= 8)) (PreH11 : (0 <= j)) (PreH12 : (j <= (0 + N_zero_rows ))),
  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  (simplex_init_vars S_zero_rows N_zero_rows (j + 1 ) 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_entail_wit_20_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (j + 1 ) 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH6 : (0 <= M_initialized_matrix_non_alias)) (PreH7 : (M_initialized_matrix_non_alias <= 16)) (PreH8 : (0 <= N_initialized_matrix_non_alias)) (PreH9 : (N_initialized_matrix_non_alias <= 8)) (PreH10 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (j + 1 ) 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_20_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH6 : (0 <= M_initialized_matrix_non_alias)) (PreH7 : (M_initialized_matrix_non_alias <= 16)) (PreH8 : (0 <= N_initialized_matrix_non_alias)) (PreH9 : (N_initialized_matrix_non_alias <= 8)) (PreH10 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH11 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH12 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (j + 1 ) 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_21_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (j + 1 ) 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH6 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH7 : (0 <= M_rejected_coefficient)) (PreH8 : (M_rejected_coefficient <= 16)) (PreH9 : (0 <= N_rejected_coefficient)) (PreH10 : (N_rejected_coefficient <= 8)) (PreH11 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (j + 1 ) 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_21_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH6 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH7 : (0 <= M_rejected_coefficient)) (PreH8 : (M_rejected_coefficient <= 16)) (PreH9 : (0 <= N_rejected_coefficient)) (PreH10 : (N_rejected_coefficient <= 8)) (PreH11 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (j + 1 ) 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_entail_wit_22_zero_rows :=
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j >= (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 0) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j >= (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  (simplex_init_vars S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
).

Definition sx_initialize_entail_wit_22_zero_rows_split_goal_spatial :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j >= (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  (simplex_init_vars S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_entail_wit_23_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_23_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_24_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_24_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_entail_wit_25_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((N_initialized_matrix_non_alias + i ) = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_initialized_matrix_non_alias) ”
  &&  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 (N_initialized_matrix_non_alias + i ) )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + ((N_initialized_matrix_non_alias + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + ((N_initialized_matrix_non_alias + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + ((N_initialized_matrix_non_alias + i ) * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i < M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  EX (x_3: Z) (x_2: Z) (x: Z),
  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_initialized_matrix_non_alias) ”
  &&  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_3)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_2)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> x)
  **  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 (N_initialized_matrix_non_alias + i ) )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + ((N_initialized_matrix_non_alias + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + ((N_initialized_matrix_non_alias + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + ((N_initialized_matrix_non_alias + i ) * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + ((N_initialized_matrix_non_alias + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_26_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i < M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ ((N_rejected_coefficient + i ) = (N_rejected_coefficient + i )) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 (N_rejected_coefficient + i ) )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + ((N_rejected_coefficient + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + ((N_rejected_coefficient + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + ((N_rejected_coefficient + i ) * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i < M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  EX (x_3: Z) (x_2: Z) (x: Z),
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rejected_coefficient) ”
  &&  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_3)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x_2)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> x)
  **  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 (N_rejected_coefficient + i ) )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + ((N_rejected_coefficient + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + ((N_rejected_coefficient + i ) * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + ((N_rejected_coefficient + i ) * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + ((N_rejected_coefficient + i ) * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_27_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (b = (N_initialized_matrix_non_alias + i ))) (PreH2 : (i < M_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (1 >= INT_MIN)) (PreH6 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH7 : (b = (N_initialized_matrix_non_alias + i ))) (PreH8 : (i < M_initialized_matrix_non_alias)) (PreH9 : (0 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH16 : (0 <= i)) (PreH17 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_27_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (b: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (1 >= INT_MIN)) (PreH6 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH7 : (b = (N_initialized_matrix_non_alias + i ))) (PreH8 : (i < M_initialized_matrix_non_alias)) (PreH9 : (0 <= M_initialized_matrix_non_alias)) (PreH10 : (M_initialized_matrix_non_alias <= 16)) (PreH11 : (0 <= N_initialized_matrix_non_alias)) (PreH12 : (N_initialized_matrix_non_alias <= 8)) (PreH13 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH16 : (0 <= i)) (PreH17 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 b )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_28_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (b = (N_rejected_coefficient + i ))) (PreH3 : (i < M_rejected_coefficient)) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i <= M_rejected_coefficient)),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> b)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (1 >= INT_MIN)) (PreH6 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH7 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH8 : (b = (N_rejected_coefficient + i ))) (PreH9 : (i < M_rejected_coefficient)) (PreH10 : (0 <= M_rejected_coefficient)) (PreH11 : (M_rejected_coefficient <= 16)) (PreH12 : (0 <= N_rejected_coefficient)) (PreH13 : (N_rejected_coefficient <= 8)) (PreH14 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH15 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH16 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH17 : (0 <= i)) (PreH18 : (i <= M_rejected_coefficient)),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_28_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (b: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (1 >= INT_MIN)) (PreH6 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH7 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH8 : (b = (N_rejected_coefficient + i ))) (PreH9 : (i < M_rejected_coefficient)) (PreH10 : (0 <= M_rejected_coefficient)) (PreH11 : (M_rejected_coefficient <= 16)) (PreH12 : (0 <= N_rejected_coefficient)) (PreH13 : (N_rejected_coefficient <= 8)) (PreH14 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH15 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH16 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH17 : (0 <= i)) (PreH18 : (i <= M_rejected_coefficient)),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i 0 )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (0 * sizeof(INT)))) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 b )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (b * sizeof(INT)))) # Int  |-> 1)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (b * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (b * sizeof(INT)))) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (b * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i 0 (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_entail_wit_29_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i < M_initialized_matrix_non_alias)) (PreH11 : (b = (N_initialized_matrix_non_alias + i ))) (PreH12 : (0 <= j)) (PreH13 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i < M_initialized_matrix_non_alias)) (PreH11 : (b = (N_initialized_matrix_non_alias + i ))) (PreH12 : (0 <= j)) (PreH13 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  EX (x_2: Z) (x: Z),
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_2)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
).

Definition sx_initialize_entail_wit_30_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i < M_rejected_coefficient)) (PreH12 : (b = (N_rejected_coefficient + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i < M_rejected_coefficient)) (PreH12 : (b = (N_rejected_coefficient + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  EX (x_2: Z) (x: Z),
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> x_2)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> x)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
).

Definition sx_initialize_entail_wit_31_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  “ (j < N_initialized_matrix_non_alias) ”
  &&  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
).

Definition sx_initialize_entail_wit_31_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
.

Definition sx_initialize_entail_wit_32_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < N_rejected_coefficient) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
).

Definition sx_initialize_entail_wit_32_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
.

Definition sx_initialize_entail_wit_33_1_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < N_rejected_coefficient)) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i (j + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH5 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH6 : (j < N_rejected_coefficient)) (PreH7 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (0 <= i)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (b = (N_rejected_coefficient + i ))) (PreH18 : (0 <= j)) (PreH19 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i (j + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_33_1_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH5 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH6 : (j < N_rejected_coefficient)) (PreH7 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (0 <= i)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (b = (N_rejected_coefficient + i ))) (PreH18 : (0 <= j)) (PreH19 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i (j + 1 ) )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_rejected_coefficient) (0)))
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i (j + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_entail_wit_33_2_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j >= N_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH4 : (0 <= M_rejected_coefficient)) (PreH5 : (M_rejected_coefficient <= 16)) (PreH6 : (0 <= N_rejected_coefficient)) (PreH7 : (N_rejected_coefficient <= 8)) (PreH8 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH9 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH10 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH11 : (0 <= i)) (PreH12 : (i < M_rejected_coefficient)) (PreH13 : (b = (N_rejected_coefficient + i ))) (PreH14 : (0 <= j)) (PreH15 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i (j + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) )
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j >= N_rejected_coefficient)) (PreH6 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH7 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (0 <= i)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (b = (N_rejected_coefficient + i ))) (PreH18 : (0 <= j)) (PreH19 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i (j + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_33_2_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j >= N_rejected_coefficient)) (PreH6 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH7 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (0 <= i)) (PreH16 : (i < M_rejected_coefficient)) (PreH17 : (b = (N_rejected_coefficient + i ))) (PreH18 : (0 <= j)) (PreH19 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i (j + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_entail_wit_34_1_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH5 : (j < N_initialized_matrix_non_alias)) (PreH6 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (0 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH14 : (0 <= i)) (PreH15 : (i < M_initialized_matrix_non_alias)) (PreH16 : (b = (N_initialized_matrix_non_alias + i ))) (PreH17 : (0 <= j)) (PreH18 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_34_1_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : ((Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH5 : (j < N_initialized_matrix_non_alias)) (PreH6 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (0 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH14 : (0 <= i)) (PreH15 : (i < M_initialized_matrix_non_alias)) (PreH16 : (b = (N_initialized_matrix_non_alias + i ))) (PreH17 : (0 <= j)) (PreH18 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + ((j + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((((i * 9 ) + j ) + 1 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_34_2_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j >= N_initialized_matrix_non_alias)) (PreH2 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i < M_initialized_matrix_non_alias)) (PreH12 : (b = (N_initialized_matrix_non_alias + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j >= N_initialized_matrix_non_alias)) (PreH6 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (0 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH14 : (0 <= i)) (PreH15 : (i < M_initialized_matrix_non_alias)) (PreH16 : (b = (N_initialized_matrix_non_alias + i ))) (PreH17 : (0 <= j)) (PreH18 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_34_2_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (0 <= INT_MAX)) (PreH3 : (1 >= INT_MIN)) (PreH4 : (0 >= INT_MIN)) (PreH5 : (j >= N_initialized_matrix_non_alias)) (PreH6 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (0 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH14 : (0 <= i)) (PreH15 : (i < M_initialized_matrix_non_alias)) (PreH16 : (b = (N_initialized_matrix_non_alias + i ))) (PreH17 : (0 <= j)) (PreH18 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i (j + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_35_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i < M_rejected_coefficient)) (PreH12 : (b = (N_rejected_coefficient + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= M_rejected_coefficient) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient (i + 1 ) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH3 : ((N_rejected_coefficient + i ) <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH6 : ((N_rejected_coefficient + i ) >= INT_MIN)) (PreH7 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH8 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (0 <= i)) (PreH17 : (i < M_rejected_coefficient)) (PreH18 : (b = (N_rejected_coefficient + i ))) (PreH19 : (0 <= j)) (PreH20 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient (i + 1 ) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_35_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH3 : ((N_rejected_coefficient + i ) <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : ((Znth ((i * 9 )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH6 : ((N_rejected_coefficient + i ) >= INT_MIN)) (PreH7 : (j >= (M_rejected_coefficient + N_rejected_coefficient ))) (PreH8 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (0 <= i)) (PreH17 : (i < M_rejected_coefficient)) (PreH18 : (b = (N_rejected_coefficient + i ))) (PreH19 : (0 <= j)) (PreH20 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient (i + 1 ) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_entail_wit_36_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i < M_initialized_matrix_non_alias)) (PreH11 : (b = (N_initialized_matrix_non_alias + i ))) (PreH12 : (0 <= j)) (PreH13 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= M_initialized_matrix_non_alias) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias (i + 1 ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH3 : ((N_initialized_matrix_non_alias + i ) <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH6 : ((N_initialized_matrix_non_alias + i ) >= INT_MIN)) (PreH7 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH8 : (0 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH15 : (0 <= i)) (PreH16 : (i < M_initialized_matrix_non_alias)) (PreH17 : (b = (N_initialized_matrix_non_alias + i ))) (PreH18 : (0 <= j)) (PreH19 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias (i + 1 ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_36_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (b: Z) (i: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH3 : ((N_initialized_matrix_non_alias + i ) <= INT_MAX)) (PreH4 : (1 >= INT_MIN)) (PreH5 : ((Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH6 : ((N_initialized_matrix_non_alias + i ) >= INT_MIN)) (PreH7 : (j >= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH8 : (0 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH15 : (0 <= i)) (PreH16 : (i < M_initialized_matrix_non_alias)) (PreH17 : (b = (N_initialized_matrix_non_alias + i ))) (PreH18 : (0 <= j)) (PreH19 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias (i + 1 ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_2 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_3 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_4 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_5 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_6 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 )) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_7 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 )) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_8 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_9 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_10 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_11 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_12 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_13 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_14 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_15 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_16 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_17 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_18 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_19 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
.

Definition sx_initialize_entail_wit_37_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (i: Z) (PreH1 : (i >= M_initialized_matrix_non_alias)) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i <= M_initialized_matrix_non_alias)),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_entail_wit_38_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  ((( &( "i" ) )) # Int  |-> i)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 )) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
).

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_1 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_2 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_3 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_4 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_5 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_6 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 )) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_7 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 )) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_8 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_9 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_10 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_11 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_12 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_13 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_14 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_15 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_16 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_17 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_18 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_19 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
.

Definition sx_initialize_entail_wit_38_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (i: Z) (PreH1 : (i >= M_rejected_coefficient)) (PreH2 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_rejected_coefficient)),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_return_wit_1_zero_rows :=
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (i >= rows)) (PreH3 : (rows = 0)) (PreH4 : (0 <= 0)) (PreH5 : (0 <= 16)) (PreH6 : (0 <= N_zero_rows)) (PreH7 : (N_zero_rows <= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 0)),
  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
|--
  “ (simplex_init_return retval 1 ) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
) \/
(
forall (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (i >= rows)) (PreH3 : (rows = 0)) (PreH4 : (0 <= 0)) (PreH5 : (0 <= 16)) (PreH6 : (0 <= N_zero_rows)) (PreH7 : (N_zero_rows <= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 0)),
  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
|--
  “ (simplex_init_return 1 1 ) ”
  &&  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
).

Definition sx_initialize_return_wit_1_zero_rows_split_goal_1 :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (i >= rows)) (PreH3 : (rows = 0)) (PreH4 : (0 <= 0)) (PreH5 : (0 <= 16)) (PreH6 : (0 <= N_zero_rows)) (PreH7 : (N_zero_rows <= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 0)),
  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
|--
  “ (simplex_init_return 1 1 ) ”
.

Definition sx_initialize_return_wit_1_zero_rows_split_goal_spatial :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : (i >= rows)) (PreH3 : (rows = 0)) (PreH4 : (0 <= 0)) (PreH5 : (0 <= 16)) (PreH6 : (0 <= N_zero_rows)) (PreH7 : (N_zero_rows <= 8)) (PreH8 : (0 <= i)) (PreH9 : (i <= 0)),
  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
|--
  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) 0 (0 + N_zero_rows ) (simplex_init_rhs ((@nil Z)) (0)) 1 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_return_wit_2_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH2 : (Forall (Z.ge (INT_MAX)) ON )) (PreH3 : (Forall (Z.le (1)) OD )) (PreH4 : (Forall (Z.ge (INT_MAX)) OD )) (PreH5 : ((Zlength (ON)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH6 : ((Zlength (OD)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (simplex_recompute_prefix (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) retval ON OD )) (PreH8 : (0 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH17 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH19 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH21 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH22 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH23 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH24 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH25 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH26 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH27 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH28 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH29 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH30 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH31 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH32 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH33 : forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) ON OD )
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (simplex_init_return retval 1 ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH2 : (Forall (Z.ge (INT_MAX)) ON )) (PreH3 : (Forall (Z.le (1)) OD )) (PreH4 : (Forall (Z.ge (INT_MAX)) OD )) (PreH5 : ((Zlength (ON)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH6 : ((Zlength (OD)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (simplex_recompute_prefix (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) retval ON OD )) (PreH8 : (0 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH17 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH19 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH21 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH22 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH23 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH24 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH25 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH26 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH27 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH28 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH29 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH30 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH31 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH32 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH33 : forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) ON OD )
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (simplex_init_return retval 1 ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH2 : (Forall (Z.ge (INT_MAX)) ON )) (PreH3 : (Forall (Z.le (1)) OD )) (PreH4 : (Forall (Z.ge (INT_MAX)) OD )) (PreH5 : ((Zlength (ON)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH6 : ((Zlength (OD)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (simplex_recompute_prefix (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) retval ON OD )) (PreH8 : (0 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH17 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH19 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH21 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH22 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH23 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH24 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH25 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH26 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH27 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH28 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH29 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH30 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH31 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH32 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH33 : forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) ON OD )
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (simplex_init_return retval 1 ) ”
.

Definition sx_initialize_return_wit_2_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH2 : (Forall (Z.ge (INT_MAX)) ON )) (PreH3 : (Forall (Z.le (1)) OD )) (PreH4 : (Forall (Z.ge (INT_MAX)) OD )) (PreH5 : ((Zlength (ON)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH6 : ((Zlength (OD)) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH7 : (simplex_recompute_prefix (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) retval ON OD )) (PreH8 : (0 <= M_initialized_matrix_non_alias)) (PreH9 : (M_initialized_matrix_non_alias <= 16)) (PreH10 : (0 <= N_initialized_matrix_non_alias)) (PreH11 : (N_initialized_matrix_non_alias <= 8)) (PreH12 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH15 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH17 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH19 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH21 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH22 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH23 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH24 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH25 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH26 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH27 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH28 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH29 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH30 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH31 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH32 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH33 : forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) ON OD )
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_return_wit_3_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH2 : (Forall (Z.ge (INT_MAX)) ON )) (PreH3 : (Forall (Z.le (1)) OD )) (PreH4 : (Forall (Z.ge (INT_MAX)) OD )) (PreH5 : ((Zlength (ON)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH6 : ((Zlength (OD)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH7 : (simplex_recompute_prefix (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) retval ON OD )) (PreH8 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH9 : (0 <= M_rejected_coefficient)) (PreH10 : (M_rejected_coefficient <= 16)) (PreH11 : (0 <= N_rejected_coefficient)) (PreH12 : (N_rejected_coefficient <= 8)) (PreH13 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH14 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH15 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH16 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH17 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH18 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH19 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH20 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH21 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH22 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH23 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH24 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH25 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH26 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH27 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH28 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH29 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH30 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH31 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH32 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH33 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH34 : forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) ON OD )
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_return retval 0 ) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
) \/
(
forall (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (N_rejected_coefficient <= INT_MAX)) (PreH2 : ((M_rejected_coefficient + N_rejected_coefficient ) <= INT_MAX)) (PreH3 : (M_rejected_coefficient <= INT_MAX)) (PreH4 : (N_rejected_coefficient >= INT_MIN)) (PreH5 : ((M_rejected_coefficient + N_rejected_coefficient ) >= INT_MIN)) (PreH6 : (M_rejected_coefficient >= INT_MIN)) (PreH7 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH8 : (Forall (Z.ge (INT_MAX)) ON )) (PreH9 : (Forall (Z.le (1)) OD )) (PreH10 : (Forall (Z.ge (INT_MAX)) OD )) (PreH11 : ((Zlength (ON)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH12 : ((Zlength (OD)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH13 : (simplex_recompute_prefix (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) retval ON OD )) (PreH14 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH15 : (0 <= M_rejected_coefficient)) (PreH16 : (M_rejected_coefficient <= 16)) (PreH17 : (0 <= N_rejected_coefficient)) (PreH18 : (N_rejected_coefficient <= 8)) (PreH19 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH20 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH21 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH22 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH23 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH24 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH25 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH26 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH27 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH28 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH29 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH30 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH31 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH32 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH33 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH34 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH35 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH36 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH37 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH38 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH39 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH40 : forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) ON OD )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_return retval 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_3_rejected_coefficient_split_goal_1 :=
forall (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (N_rejected_coefficient <= INT_MAX)) (PreH2 : ((M_rejected_coefficient + N_rejected_coefficient ) <= INT_MAX)) (PreH3 : (M_rejected_coefficient <= INT_MAX)) (PreH4 : (N_rejected_coefficient >= INT_MIN)) (PreH5 : ((M_rejected_coefficient + N_rejected_coefficient ) >= INT_MIN)) (PreH6 : (M_rejected_coefficient >= INT_MIN)) (PreH7 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH8 : (Forall (Z.ge (INT_MAX)) ON )) (PreH9 : (Forall (Z.le (1)) OD )) (PreH10 : (Forall (Z.ge (INT_MAX)) OD )) (PreH11 : ((Zlength (ON)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH12 : ((Zlength (OD)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH13 : (simplex_recompute_prefix (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) retval ON OD )) (PreH14 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH15 : (0 <= M_rejected_coefficient)) (PreH16 : (M_rejected_coefficient <= 16)) (PreH17 : (0 <= N_rejected_coefficient)) (PreH18 : (N_rejected_coefficient <= 8)) (PreH19 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH20 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH21 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH22 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH23 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH24 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH25 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH26 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH27 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH28 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH29 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH30 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH31 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH32 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH33 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH34 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH35 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH36 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH37 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH38 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH39 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH40 : forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) ON OD )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_return retval 0 ) ”
.

Definition sx_initialize_return_wit_3_rejected_coefficient_split_goal_spatial :=
forall (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (OD: (@list Z)) (ON: (@list Z)) (retval: Z) (PreH1 : (N_rejected_coefficient <= INT_MAX)) (PreH2 : ((M_rejected_coefficient + N_rejected_coefficient ) <= INT_MAX)) (PreH3 : (M_rejected_coefficient <= INT_MAX)) (PreH4 : (N_rejected_coefficient >= INT_MIN)) (PreH5 : ((M_rejected_coefficient + N_rejected_coefficient ) >= INT_MIN)) (PreH6 : (M_rejected_coefficient >= INT_MIN)) (PreH7 : (Forall (Z.le ((-INT_MAX))) ON )) (PreH8 : (Forall (Z.ge (INT_MAX)) ON )) (PreH9 : (Forall (Z.le (1)) OD )) (PreH10 : (Forall (Z.ge (INT_MAX)) OD )) (PreH11 : ((Zlength (ON)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH12 : ((Zlength (OD)) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH13 : (simplex_recompute_prefix (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) retval ON OD )) (PreH14 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH15 : (0 <= M_rejected_coefficient)) (PreH16 : (M_rejected_coefficient <= 16)) (PreH17 : (0 <= N_rejected_coefficient)) (PreH18 : (N_rejected_coefficient <= 8)) (PreH19 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH20 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH21 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH22 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH23 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH24 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH25 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH26 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH27 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH28 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH29 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH30 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH31 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH32 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH33 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH34 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH35 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH36 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH37 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH38 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH39 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH40 : forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) ON OD )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  TT && emp 
.

Definition sx_initialize_return_wit_4_initialized_matrix_non_alias :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) = ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_initialized_matrix_non_alias)) (PreH3 : (0 <= M_initialized_matrix_non_alias)) (PreH4 : (M_initialized_matrix_non_alias <= 16)) (PreH5 : (0 <= N_initialized_matrix_non_alias)) (PreH6 : (N_initialized_matrix_non_alias <= 8)) (PreH7 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH10 : (0 <= i)) (PreH11 : (i <= M_initialized_matrix_non_alias)) (PreH12 : (i < M_initialized_matrix_non_alias)) (PreH13 : (0 <= j)) (PreH14 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH15 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (simplex_init_return 0 1 ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) = ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_initialized_matrix_non_alias)) (PreH5 : (0 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH12 : (0 <= i)) (PreH13 : (i <= M_initialized_matrix_non_alias)) (PreH14 : (i < M_initialized_matrix_non_alias)) (PreH15 : (0 <= j)) (PreH16 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH17 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (simplex_init_return 0 1 ) ”
  &&  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
).

Definition sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) = ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_initialized_matrix_non_alias)) (PreH5 : (0 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH12 : (0 <= i)) (PreH13 : (i <= M_initialized_matrix_non_alias)) (PreH14 : (i < M_initialized_matrix_non_alias)) (PreH15 : (0 <= j)) (PreH16 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH17 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (simplex_init_return 0 1 ) ”
.

Definition sx_initialize_return_wit_4_initialized_matrix_non_alias_split_goal_spatial :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)) = ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_initialized_matrix_non_alias)) (PreH5 : (0 <= M_initialized_matrix_non_alias)) (PreH6 : (M_initialized_matrix_non_alias <= 16)) (PreH7 : (0 <= N_initialized_matrix_non_alias)) (PreH8 : (N_initialized_matrix_non_alias <= 8)) (PreH9 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH10 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH12 : (0 <= i)) (PreH13 : (i <= M_initialized_matrix_non_alias)) (PreH14 : (i < M_initialized_matrix_non_alias)) (PreH15 : (0 <= j)) (PreH16 : (j <= (N_initialized_matrix_non_alias + 1 ))) (PreH17 : forall (x: Z), forall (y: Z), ((((((0 <= x) /\ (x < M_initialized_matrix_non_alias)) /\ (0 <= y)) /\ (y <= N_initialized_matrix_non_alias)) /\ ((x < i) \/ ((x = i) /\ (y < j)))) -> ((Znth (((x * 9 ) + y )) (A_initialized_matrix_non_alias) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias i j )
  **  ((((C_initialized_matrix_non_alias + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_initialized_matrix_non_alias) (0)))
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |->_)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |->_)
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) 1 )
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_return_wit_5_rejected_coefficient :=
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) = ((-INT_MAX) - 1 ))) (PreH2 : (j <= N_rejected_coefficient)) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= x)) (PreH11 : (x < M_rejected_coefficient)) (PreH12 : (0 <= y)) (PreH13 : (y <= N_rejected_coefficient)) (PreH14 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH15 : (0 <= i)) (PreH16 : (i <= M_rejected_coefficient)) (PreH17 : (i < M_rejected_coefficient)) (PreH18 : (0 <= j)) (PreH19 : (j <= (N_rejected_coefficient + 1 ))) (PreH20 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
|--
  “ (simplex_init_return 0 0 ) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
) \/
(
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) = ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_rejected_coefficient)) (PreH5 : (0 <= M_rejected_coefficient)) (PreH6 : (M_rejected_coefficient <= 16)) (PreH7 : (0 <= N_rejected_coefficient)) (PreH8 : (N_rejected_coefficient <= 8)) (PreH9 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH10 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH12 : (0 <= x)) (PreH13 : (x < M_rejected_coefficient)) (PreH14 : (0 <= y)) (PreH15 : (y <= N_rejected_coefficient)) (PreH16 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH17 : (0 <= i)) (PreH18 : (i <= M_rejected_coefficient)) (PreH19 : (i < M_rejected_coefficient)) (PreH20 : (0 <= j)) (PreH21 : (j <= (N_rejected_coefficient + 1 ))) (PreH22 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
|--
  “ (simplex_init_return 0 0 ) ”
  &&  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
).

Definition sx_initialize_return_wit_5_rejected_coefficient_split_goal_1 :=
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) = ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_rejected_coefficient)) (PreH5 : (0 <= M_rejected_coefficient)) (PreH6 : (M_rejected_coefficient <= 16)) (PreH7 : (0 <= N_rejected_coefficient)) (PreH8 : (N_rejected_coefficient <= 8)) (PreH9 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH10 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH12 : (0 <= x)) (PreH13 : (x < M_rejected_coefficient)) (PreH14 : (0 <= y)) (PreH15 : (y <= N_rejected_coefficient)) (PreH16 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH17 : (0 <= i)) (PreH18 : (i <= M_rejected_coefficient)) (PreH19 : (i < M_rejected_coefficient)) (PreH20 : (0 <= j)) (PreH21 : (j <= (N_rejected_coefficient + 1 ))) (PreH22 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
|--
  “ (simplex_init_return 0 0 ) ”
.

Definition sx_initialize_return_wit_5_rejected_coefficient_split_goal_spatial :=
forall (C_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (x: Z) (y: Z) (j: Z) (i: Z) (PreH1 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) <= INT_MAX)) (PreH2 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) >= INT_MIN)) (PreH3 : ((Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)) = ((-INT_MAX) - 1 ))) (PreH4 : (j <= N_rejected_coefficient)) (PreH5 : (0 <= M_rejected_coefficient)) (PreH6 : (M_rejected_coefficient <= 16)) (PreH7 : (0 <= N_rejected_coefficient)) (PreH8 : (N_rejected_coefficient <= 8)) (PreH9 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH10 : (Forall (Z.le ((INT_MIN))) A_rejected_coefficient )) (PreH11 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH12 : (0 <= x)) (PreH13 : (x < M_rejected_coefficient)) (PreH14 : (0 <= y)) (PreH15 : (y <= N_rejected_coefficient)) (PreH16 : ((Znth (((x * 9 ) + y )) (A_rejected_coefficient) (0)) = (INT_MIN))) (PreH17 : (0 <= i)) (PreH18 : (i <= M_rejected_coefficient)) (PreH19 : (i < M_rejected_coefficient)) (PreH20 : (0 <= j)) (PreH21 : (j <= (N_rejected_coefficient + 1 ))) (PreH22 : forall (x_2: Z), forall (y_2: Z), ((((((0 <= x_2) /\ (x_2 < M_rejected_coefficient)) /\ (0 <= y_2)) /\ (y_2 <= N_rejected_coefficient)) /\ ((x_2 < i) \/ ((x_2 = i) /\ (y_2 < j)))) -> ((Znth (((x_2 * 9 ) + y_2 )) (A_rejected_coefficient) (0)) <> (INT_MIN)))),
  (simplex_init_input_except C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient i j )
  **  ((((C_rejected_coefficient + (i * (9 * sizeof(INT)))) + (j * sizeof(INT)))) # Int  |-> (Znth (((i * 9 ) + j )) (A_rejected_coefficient) (0)))
|--
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
.

Definition sx_initialize_return_wit_6_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_6_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre < 0)) (PreH2 : (rows_pre <= 16)) (PreH3 : (rows_pre >= 0)) (PreH4 : (s_pre = S_invalid_dimensions)) (PreH5 : (c_pre = C_invalid_dimensions)) (PreH6 : (rows_pre = M_invalid_dimensions)) (PreH7 : (inputs_pre = N_invalid_dimensions)) (PreH8 : (inputs_pre < 0)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_7_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre > 8)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre > 8)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_7_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre > 8)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_8_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_8_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (inputs_pre < 0)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_9_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_9_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre < 0)) (PreH2 : (s_pre = S_invalid_dimensions)) (PreH3 : (c_pre = C_invalid_dimensions)) (PreH4 : (rows_pre = M_invalid_dimensions)) (PreH5 : (inputs_pre = N_invalid_dimensions)) (PreH6 : (rows_pre < 0)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_10_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (rows_pre > 16)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (rows_pre > 16)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_10_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (rows_pre > 16)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_11_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre < 0)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_11_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre < 0)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_12_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre > 8)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre > 8)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_12_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (rows_pre > 16)) (PreH2 : (rows_pre >= 0)) (PreH3 : (s_pre = S_invalid_dimensions)) (PreH4 : (c_pre = C_invalid_dimensions)) (PreH5 : (rows_pre = M_invalid_dimensions)) (PreH6 : (inputs_pre = N_invalid_dimensions)) (PreH7 : (inputs_pre > 8)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_return_wit_13_invalid_dimensions :=
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_invalid_dimensions)) (PreH6 : (c_pre = C_invalid_dimensions)) (PreH7 : (rows_pre = M_invalid_dimensions)) (PreH8 : (inputs_pre = N_invalid_dimensions)) (PreH9 : (inputs_pre > 8)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
) \/
(
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_invalid_dimensions)) (PreH6 : (c_pre = C_invalid_dimensions)) (PreH7 : (rows_pre = M_invalid_dimensions)) (PreH8 : (inputs_pre = N_invalid_dimensions)) (PreH9 : (inputs_pre > 8)),
  TT && emp 
|--
  “ (simplex_init_return 0 0 ) ”
  &&  emp
).

Definition sx_initialize_return_wit_13_invalid_dimensions_split_goal_1 :=
forall (C_invalid_dimensions: Z) (S_invalid_dimensions: Z) (N_invalid_dimensions: Z) (M_invalid_dimensions: Z) (s_pre: Z) (rows_pre: Z) (inputs_pre: Z) (c_pre: Z) (PreH1 : (inputs_pre > 8)) (PreH2 : (inputs_pre >= 0)) (PreH3 : (rows_pre <= 16)) (PreH4 : (rows_pre >= 0)) (PreH5 : (s_pre = S_invalid_dimensions)) (PreH6 : (c_pre = C_invalid_dimensions)) (PreH7 : (rows_pre = M_invalid_dimensions)) (PreH8 : (inputs_pre = N_invalid_dimensions)) (PreH9 : (inputs_pre > 8)),
  (simplex_init_return 0 0 )
.

Definition sx_initialize_partial_solve_wit_1_zero_rows :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (j < (0 + N_zero_rows )) ”
  &&  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (0 + N_zero_rows )) ”
  &&  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_partial_solve_wit_2_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_partial_solve_wit_3_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_partial_solve_wit_4_zero_rows :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (j < (0 + N_zero_rows )) ”
  &&  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (0 + N_zero_rows )) ”
  &&  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_partial_solve_wit_5_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_partial_solve_wit_6_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_partial_solve_wit_7_zero_rows :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (j: Z) (rows: Z) (PreH1 : (j < (0 + N_zero_rows ))) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= j)) (PreH8 : (j <= (0 + N_zero_rows ))),
  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
|--
  “ (j < (0 + N_zero_rows )) ”
  &&  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (0 + N_zero_rows )) ”
  &&  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_zero_rows)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars_except S_zero_rows N_zero_rows j 0 (0 + N_zero_rows ) (@nil Z) 0 j )
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_zero_rows)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows 0 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_partial_solve_wit_8_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= j)) (PreH10 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars_except S_initialized_matrix_non_alias N_initialized_matrix_non_alias j 0 (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 j )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias 0 M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_partial_solve_wit_9_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= j)) (PreH11 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "value") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "upper") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> 0)
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "lower") + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars_except S_rejected_coefficient N_rejected_coefficient j 0 (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 j )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_lower") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "has_upper") + (j * sizeof(INT)))) # Int  |-> 0)
  **  (simplex_init_rows S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient 0 M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_partial_solve_wit_10_rejected_coefficient :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (j < (M_rejected_coefficient + N_rejected_coefficient ))) (PreH3 : (0 <= M_rejected_coefficient)) (PreH4 : (M_rejected_coefficient <= 16)) (PreH5 : (0 <= N_rejected_coefficient)) (PreH6 : (N_rejected_coefficient <= 8)) (PreH7 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH8 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH9 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH10 : (0 <= i)) (PreH11 : (i < M_rejected_coefficient)) (PreH12 : (b = (N_rejected_coefficient + i ))) (PreH13 : (0 <= j)) (PreH14 : (j <= (M_rejected_coefficient + N_rejected_coefficient ))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (j < (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rejected_coefficient) ”
  &&  “ (b = (N_rejected_coefficient + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((((&((S_rejected_coefficient)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (simplex_init_vars S_rejected_coefficient N_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (i + 1 ) (M_rejected_coefficient + N_rejected_coefficient ) A_rejected_coefficient 0 )
  **  (simplex_init_rows_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) i )
  **  (((&((S_rejected_coefficient)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_rejected_coefficient + i ))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_rejected_coefficient) (0)))
  **  ((&(((&((S_rejected_coefficient)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_rejected_coefficient A_rejected_coefficient N_rejected_coefficient i j (M_rejected_coefficient + N_rejected_coefficient ) j )
.

Definition sx_initialize_partial_solve_wit_11_initialized_matrix_non_alias :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (j: Z) (i: Z) (b: Z) (PreH1 : (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH2 : (0 <= M_initialized_matrix_non_alias)) (PreH3 : (M_initialized_matrix_non_alias <= 16)) (PreH4 : (0 <= N_initialized_matrix_non_alias)) (PreH5 : (N_initialized_matrix_non_alias <= 8)) (PreH6 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH9 : (0 <= i)) (PreH10 : (i < M_initialized_matrix_non_alias)) (PreH11 : (b = (N_initialized_matrix_non_alias + i ))) (PreH12 : (0 <= j)) (PreH13 : (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
|--
  “ (j < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_initialized_matrix_non_alias) ”
  &&  “ (b = (N_initialized_matrix_non_alias + i )) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |->_)
  **  ((&((((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "a") + (i * (24 * sizeof( "SxRat" )))) + (j * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |->_)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (simplex_init_vars S_initialized_matrix_non_alias N_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (i + 1 ) (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) A_initialized_matrix_non_alias 0 )
  **  (simplex_init_rows_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) i )
  **  (((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") + (i * sizeof(INT)))) # Int  |-> (N_initialized_matrix_non_alias + i ))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "num")) # Int  |-> (Znth ((i * 9 )) (A_initialized_matrix_non_alias) (0)))
  **  ((&(((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rhs") + (i * sizeof( "SxRat" ))))  # "SxRat" ->ₛ "den")) # Int  |-> 1)
  **  (simplex_init_a_row_except S_initialized_matrix_non_alias A_initialized_matrix_non_alias N_initialized_matrix_non_alias i j (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) j )
.

Definition sx_initialize_partial_solve_wit_12_zero_rows_pure :=
forall (C_zero_rows: Z) (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i >= rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)),
  ((( &( "c" ) )) # Ptr  |-> C_zero_rows)
  **  ((( &( "rows" ) )) # Int  |-> rows)
  **  ((( &( "inputs" ) )) # Int  |-> N_zero_rows)
  **  ((( &( "s" ) )) # Ptr  |-> S_zero_rows)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (S_zero_rows = S_zero_rows) ”
.

Definition sx_initialize_partial_solve_wit_12_zero_rows_aux :=
forall (S_zero_rows: Z) (N_zero_rows: Z) (i: Z) (rows: Z) (PreH1 : (i >= rows)) (PreH2 : (rows = 0)) (PreH3 : (0 <= 0)) (PreH4 : (0 <= 16)) (PreH5 : (0 <= N_zero_rows)) (PreH6 : (N_zero_rows <= 8)) (PreH7 : (0 <= i)) (PreH8 : (i <= 0)),
  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
|--
  “ (S_zero_rows = S_zero_rows) ”
  &&  “ (i >= rows) ”
  &&  “ (rows = 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= 16) ”
  &&  “ (0 <= N_zero_rows) ”
  &&  “ (N_zero_rows <= 8) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= 0) ”
  &&  ((&((S_zero_rows)  # "SxState" ->ₛ "rows")) # Int  |-> 0)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "inputs")) # Int  |-> N_zero_rows)
  **  ((&((S_zero_rows)  # "SxState" ->ₛ "vars")) # Int  |-> (0 + N_zero_rows ))
  **  (simplex_init_vars S_zero_rows N_zero_rows (0 + N_zero_rows ) i (0 + N_zero_rows ) (@nil Z) 0 )
  **  (simplex_init_rows S_zero_rows (@nil Z) N_zero_rows i 0 (0 + N_zero_rows ) )
.

Definition sx_initialize_partial_solve_wit_12_zero_rows := sx_initialize_partial_solve_wit_12_zero_rows_pure -> sx_initialize_partial_solve_wit_12_zero_rows_aux.

Definition sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure :=
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (PreH1 : (0 <= M_initialized_matrix_non_alias)) (PreH2 : (M_initialized_matrix_non_alias <= 16)) (PreH3 : (0 <= N_initialized_matrix_non_alias)) (PreH4 : (N_initialized_matrix_non_alias <= 8)) (PreH5 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH6 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH7 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH9 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH10 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH11 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH12 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH13 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH14 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH15 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH17 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH18 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH19 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH20 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH21 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH22 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH23 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH24 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH25 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (S_initialized_matrix_non_alias = S_initialized_matrix_non_alias) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) <= 24) ”
  &&  “ ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) + N_initialized_matrix_non_alias ) <= 24) ”
  &&  “ (0 <= ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) + N_initialized_matrix_non_alias )) ”
) \/
(
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (PreH1 : ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) <= INT_MAX)) (PreH2 : (N_initialized_matrix_non_alias <= INT_MAX)) (PreH3 : (M_initialized_matrix_non_alias <= INT_MAX)) (PreH4 : ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) >= INT_MIN)) (PreH5 : (N_initialized_matrix_non_alias >= INT_MIN)) (PreH6 : (M_initialized_matrix_non_alias >= INT_MIN)) (PreH7 : (0 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH15 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH17 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH18 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH19 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH20 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH21 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH22 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH23 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH24 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH25 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH26 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH27 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH28 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH29 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH30 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH31 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH32 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
).

Definition sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure_split_goal_1 :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (PreH1 : ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) <= INT_MAX)) (PreH2 : (N_initialized_matrix_non_alias <= INT_MAX)) (PreH3 : (M_initialized_matrix_non_alias <= INT_MAX)) (PreH4 : ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) >= INT_MIN)) (PreH5 : (N_initialized_matrix_non_alias >= INT_MIN)) (PreH6 : (M_initialized_matrix_non_alias >= INT_MIN)) (PreH7 : (0 <= M_initialized_matrix_non_alias)) (PreH8 : (M_initialized_matrix_non_alias <= 16)) (PreH9 : (0 <= N_initialized_matrix_non_alias)) (PreH10 : (N_initialized_matrix_non_alias <= 8)) (PreH11 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH12 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH13 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH14 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH15 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH17 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH18 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH19 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH20 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH21 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH22 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH23 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH24 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH25 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH26 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH27 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH28 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH29 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH30 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH31 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH32 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  ((( &( "s" ) )) # Ptr  |-> S_initialized_matrix_non_alias)
  **  ((( &( "rows" ) )) # Int  |-> M_initialized_matrix_non_alias)
  **  ((( &( "inputs" ) )) # Int  |-> N_initialized_matrix_non_alias)
  **  ((( &( "c" ) )) # Ptr  |-> C_initialized_matrix_non_alias)
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
.

Definition sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_aux :=
forall (C_initialized_matrix_non_alias: Z) (S_initialized_matrix_non_alias: Z) (N_initialized_matrix_non_alias: Z) (M_initialized_matrix_non_alias: Z) (A_initialized_matrix_non_alias: (@list Z)) (PreH1 : (0 <= M_initialized_matrix_non_alias)) (PreH2 : (M_initialized_matrix_non_alias <= 16)) (PreH3 : (0 <= N_initialized_matrix_non_alias)) (PreH4 : (N_initialized_matrix_non_alias <= 8)) (PreH5 : ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 ))) (PreH6 : (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias )) (PreH7 : (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias )) (PreH8 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH9 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) )) (PreH10 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH11 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )) (PreH12 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH13 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )) (PreH14 : (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH15 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) )) (PreH16 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH17 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH18 : (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH19 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )) (PreH20 : ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 ))) (PreH21 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 ))) (PreH22 : ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH23 : ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias)) (PreH24 : ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH25 : ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (PreH26 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))),
  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
|--
  “ (S_initialized_matrix_non_alias = S_initialized_matrix_non_alias) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) <= 24) ”
  &&  “ ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ (((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) + N_initialized_matrix_non_alias ) <= 24) ”
  &&  “ (0 <= ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) + N_initialized_matrix_non_alias )) ”
  &&  “ (0 <= M_initialized_matrix_non_alias) ”
  &&  “ (M_initialized_matrix_non_alias <= 16) ”
  &&  “ (0 <= N_initialized_matrix_non_alias) ”
  &&  “ (N_initialized_matrix_non_alias <= 8) ”
  &&  “ ((Zlength (A_initialized_matrix_non_alias)) = (M_initialized_matrix_non_alias * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_initialized_matrix_non_alias ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_initialized_matrix_non_alias)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) ) ”
  &&  “ ((Zlength ((simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))))) = (M_initialized_matrix_non_alias * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_ones (M_initialized_matrix_non_alias)))) = M_initialized_matrix_non_alias) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))))) = (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_initialized_matrix_non_alias)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias))) (0)) < (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias )))) ”
  &&  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "rows")) # Int  |-> M_initialized_matrix_non_alias)
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "vars")) # Int  |-> (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "basic") M_initialized_matrix_non_alias (simplex_init_basic (N_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) )
  **  (IntArray.full &((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "is_basic") (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_flags (N_initialized_matrix_non_alias) ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_recompute_rhs S_initialized_matrix_non_alias M_initialized_matrix_non_alias (simplex_init_rhs (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias)) (simplex_init_ones (M_initialized_matrix_non_alias)) )
  **  (simplex_recompute_matrix S_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_an (A_initialized_matrix_non_alias) (M_initialized_matrix_non_alias) (N_initialized_matrix_non_alias)) (simplex_init_ones ((M_initialized_matrix_non_alias * 24 ))) )
  **  (simplex_recompute_values S_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) (simplex_init_zeroes ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) (simplex_init_ones ((M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ))) )
  **  (simplex_init_input C_initialized_matrix_non_alias A_initialized_matrix_non_alias M_initialized_matrix_non_alias N_initialized_matrix_non_alias )
  **  ((&((S_initialized_matrix_non_alias)  # "SxState" ->ₛ "inputs")) # Int  |-> N_initialized_matrix_non_alias)
  **  (simplex_init_bounds S_initialized_matrix_non_alias N_initialized_matrix_non_alias M_initialized_matrix_non_alias (M_initialized_matrix_non_alias + N_initialized_matrix_non_alias ) )
.

Definition sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias := sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure -> sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_aux.

Definition sx_initialize_partial_solve_wit_14_rejected_coefficient_pure :=
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH10 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH11 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH12 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH13 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH14 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH15 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH17 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH19 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH21 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH22 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH23 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH24 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH25 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH26 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_rejected_coefficient)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ (S_rejected_coefficient = S_rejected_coefficient) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((M_rejected_coefficient + N_rejected_coefficient ) <= 24) ”
  &&  “ ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) + N_rejected_coefficient ) <= 24) ”
  &&  “ (0 <= ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) + N_rejected_coefficient )) ”
) \/
(
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : ((M_rejected_coefficient + N_rejected_coefficient ) <= INT_MAX)) (PreH2 : (N_rejected_coefficient <= INT_MAX)) (PreH3 : (M_rejected_coefficient <= INT_MAX)) (PreH4 : ((M_rejected_coefficient + N_rejected_coefficient ) >= INT_MIN)) (PreH5 : (N_rejected_coefficient >= INT_MIN)) (PreH6 : (M_rejected_coefficient >= INT_MIN)) (PreH7 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH17 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH19 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH21 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH22 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH23 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH24 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH25 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH26 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH27 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH28 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH29 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH30 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH31 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH32 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH33 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_rejected_coefficient)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
).

Definition sx_initialize_partial_solve_wit_14_rejected_coefficient_pure_split_goal_1 :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : ((M_rejected_coefficient + N_rejected_coefficient ) <= INT_MAX)) (PreH2 : (N_rejected_coefficient <= INT_MAX)) (PreH3 : (M_rejected_coefficient <= INT_MAX)) (PreH4 : ((M_rejected_coefficient + N_rejected_coefficient ) >= INT_MIN)) (PreH5 : (N_rejected_coefficient >= INT_MIN)) (PreH6 : (M_rejected_coefficient >= INT_MIN)) (PreH7 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH8 : (0 <= M_rejected_coefficient)) (PreH9 : (M_rejected_coefficient <= 16)) (PreH10 : (0 <= N_rejected_coefficient)) (PreH11 : (N_rejected_coefficient <= 8)) (PreH12 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH13 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH14 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH15 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH17 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH19 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH21 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH22 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH23 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH24 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH25 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH26 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH27 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH28 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH29 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH30 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH31 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH32 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH33 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_rejected_coefficient)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  ((( &( "s" ) )) # Ptr  |-> S_rejected_coefficient)
  **  ((( &( "rows" ) )) # Int  |-> M_rejected_coefficient)
  **  ((( &( "inputs" ) )) # Int  |-> N_rejected_coefficient)
  **  ((( &( "c" ) )) # Ptr  |-> C_rejected_coefficient)
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
|--
  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
.

Definition sx_initialize_partial_solve_wit_14_rejected_coefficient_aux :=
forall (C_rejected_coefficient: Z) (S_rejected_coefficient: Z) (N_rejected_coefficient: Z) (M_rejected_coefficient: Z) (A_rejected_coefficient: (@list Z)) (PreH1 : (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient )) (PreH2 : (0 <= M_rejected_coefficient)) (PreH3 : (M_rejected_coefficient <= 16)) (PreH4 : (0 <= N_rejected_coefficient)) (PreH5 : (N_rejected_coefficient <= 8)) (PreH6 : ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 ))) (PreH7 : (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient )) (PreH8 : (Forall (Z.ge (INT_MAX)) A_rejected_coefficient )) (PreH9 : (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH10 : (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) )) (PreH11 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH12 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )) (PreH13 : (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH14 : (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) )) (PreH15 : (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH16 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) )) (PreH17 : (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH18 : (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH19 : (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH20 : (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )) (PreH21 : ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 ))) (PreH22 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 ))) (PreH23 : ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH24 : ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient)) (PreH25 : ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH26 : ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient ))) (PreH27 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_rejected_coefficient)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient ))))),
  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
|--
  “ (S_rejected_coefficient = S_rejected_coefficient) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((M_rejected_coefficient + N_rejected_coefficient ) <= 24) ”
  &&  “ ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < M_rejected_coefficient)) -> ((0 <= (Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ (((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) + N_rejected_coefficient ) <= 24) ”
  &&  “ (0 <= ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) + N_rejected_coefficient )) ”
  &&  “ (simplex_init_unreachable M_rejected_coefficient N_rejected_coefficient ) ”
  &&  “ (0 <= M_rejected_coefficient) ”
  &&  “ (M_rejected_coefficient <= 16) ”
  &&  “ (0 <= N_rejected_coefficient) ”
  &&  “ (N_rejected_coefficient <= 8) ”
  &&  “ ((Zlength (A_rejected_coefficient)) = (M_rejected_coefficient * 9 )) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) A_rejected_coefficient ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones (M_rejected_coefficient)) ) ”
  &&  “ (Forall (Z.le ((-INT_MAX))) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.le (1)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ (Forall (Z.ge (INT_MAX)) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) ) ”
  &&  “ ((Zlength ((simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient * 24 ))))) = (M_rejected_coefficient * 24 )) ”
  &&  “ ((Zlength ((simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_ones (M_rejected_coefficient)))) = M_rejected_coefficient) ”
  &&  “ ((Zlength ((simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ ((Zlength ((simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))))) = (M_rejected_coefficient + N_rejected_coefficient )) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < M_rejected_coefficient)) -> ((0 <= (Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0))) /\ ((Znth (k_2) ((simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient))) (0)) < (M_rejected_coefficient + N_rejected_coefficient )))) ”
  &&  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "rows")) # Int  |-> M_rejected_coefficient)
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "vars")) # Int  |-> (M_rejected_coefficient + N_rejected_coefficient ))
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "basic") M_rejected_coefficient (simplex_init_basic (N_rejected_coefficient) (M_rejected_coefficient)) )
  **  (IntArray.full &((S_rejected_coefficient)  # "SxState" ->ₛ "is_basic") (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_flags (N_rejected_coefficient) ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_recompute_rhs S_rejected_coefficient M_rejected_coefficient (simplex_init_rhs (A_rejected_coefficient) (M_rejected_coefficient)) (simplex_init_ones (M_rejected_coefficient)) )
  **  (simplex_recompute_matrix S_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_an (A_rejected_coefficient) (M_rejected_coefficient) (N_rejected_coefficient)) (simplex_init_ones ((M_rejected_coefficient * 24 ))) )
  **  (simplex_recompute_values S_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) (simplex_init_zeroes ((M_rejected_coefficient + N_rejected_coefficient ))) (simplex_init_ones ((M_rejected_coefficient + N_rejected_coefficient ))) )
  **  (simplex_init_input C_rejected_coefficient A_rejected_coefficient M_rejected_coefficient N_rejected_coefficient )
  **  ((&((S_rejected_coefficient)  # "SxState" ->ₛ "inputs")) # Int  |-> N_rejected_coefficient)
  **  (simplex_init_bounds S_rejected_coefficient N_rejected_coefficient M_rejected_coefficient (M_rejected_coefficient + N_rejected_coefficient ) )
.

Definition sx_initialize_partial_solve_wit_14_rejected_coefficient := sx_initialize_partial_solve_wit_14_rejected_coefficient_pure -> sx_initialize_partial_solve_wit_14_rejected_coefficient_aux.

Module Type VC_Correct.


Axiom proof_of_sx_initialize_safety_wit_1_invalid_dimensions : sx_initialize_safety_wit_1_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_2_invalid_dimensions : sx_initialize_safety_wit_2_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_3_invalid_dimensions : sx_initialize_safety_wit_3_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_4_invalid_dimensions : sx_initialize_safety_wit_4_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_5_rejected_coefficient : sx_initialize_safety_wit_5_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_6_initialized_matrix_non_alias : sx_initialize_safety_wit_6_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_7_zero_rows : sx_initialize_safety_wit_7_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_8_invalid_dimensions : sx_initialize_safety_wit_8_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_9_invalid_dimensions : sx_initialize_safety_wit_9_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_10_rejected_coefficient : sx_initialize_safety_wit_10_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_11_initialized_matrix_non_alias : sx_initialize_safety_wit_11_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_12_zero_rows : sx_initialize_safety_wit_12_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_13_zero_rows : sx_initialize_safety_wit_13_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_14_initialized_matrix_non_alias : sx_initialize_safety_wit_14_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_15_rejected_coefficient : sx_initialize_safety_wit_15_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_16_invalid_dimensions : sx_initialize_safety_wit_16_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_17_invalid_dimensions : sx_initialize_safety_wit_17_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_18_invalid_dimensions : sx_initialize_safety_wit_18_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_19_zero_rows : sx_initialize_safety_wit_19_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_20_initialized_matrix_non_alias : sx_initialize_safety_wit_20_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_21_rejected_coefficient : sx_initialize_safety_wit_21_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_22_invalid_dimensions : sx_initialize_safety_wit_22_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_23_zero_rows : sx_initialize_safety_wit_23_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_24_initialized_matrix_non_alias : sx_initialize_safety_wit_24_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_25_rejected_coefficient : sx_initialize_safety_wit_25_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_26_invalid_dimensions : sx_initialize_safety_wit_26_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_27_invalid_dimensions : sx_initialize_safety_wit_27_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_28_zero_rows : sx_initialize_safety_wit_28_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_29_initialized_matrix_non_alias : sx_initialize_safety_wit_29_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_30_rejected_coefficient : sx_initialize_safety_wit_30_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_31_invalid_dimensions : sx_initialize_safety_wit_31_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_32_invalid_dimensions : sx_initialize_safety_wit_32_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_33_zero_rows : sx_initialize_safety_wit_33_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_34_initialized_matrix_non_alias : sx_initialize_safety_wit_34_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_35_rejected_coefficient : sx_initialize_safety_wit_35_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_36_invalid_dimensions : sx_initialize_safety_wit_36_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_37_zero_rows : sx_initialize_safety_wit_37_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_38_initialized_matrix_non_alias : sx_initialize_safety_wit_38_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_39_rejected_coefficient : sx_initialize_safety_wit_39_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_40_invalid_dimensions : sx_initialize_safety_wit_40_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_41_invalid_dimensions : sx_initialize_safety_wit_41_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_42_invalid_dimensions : sx_initialize_safety_wit_42_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_43_invalid_dimensions : sx_initialize_safety_wit_43_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_44_invalid_dimensions : sx_initialize_safety_wit_44_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_45_invalid_dimensions : sx_initialize_safety_wit_45_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_46_invalid_dimensions : sx_initialize_safety_wit_46_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_47_invalid_dimensions : sx_initialize_safety_wit_47_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_48_invalid_dimensions : sx_initialize_safety_wit_48_invalid_dimensions.
Axiom proof_of_sx_initialize_safety_wit_49_rejected_coefficient : sx_initialize_safety_wit_49_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_50_initialized_matrix_non_alias : sx_initialize_safety_wit_50_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_51_zero_rows : sx_initialize_safety_wit_51_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_52_zero_rows : sx_initialize_safety_wit_52_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_53_rejected_coefficient : sx_initialize_safety_wit_53_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_54_initialized_matrix_non_alias : sx_initialize_safety_wit_54_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_55_rejected_coefficient : sx_initialize_safety_wit_55_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_56_initialized_matrix_non_alias : sx_initialize_safety_wit_56_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_57_rejected_coefficient : sx_initialize_safety_wit_57_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_58_initialized_matrix_non_alias : sx_initialize_safety_wit_58_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_59_initialized_matrix_non_alias : sx_initialize_safety_wit_59_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_60_rejected_coefficient : sx_initialize_safety_wit_60_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_61_initialized_matrix_non_alias : sx_initialize_safety_wit_61_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_62_rejected_coefficient : sx_initialize_safety_wit_62_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_63_initialized_matrix_non_alias : sx_initialize_safety_wit_63_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_64_rejected_coefficient : sx_initialize_safety_wit_64_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_65_rejected_coefficient : sx_initialize_safety_wit_65_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_66_initialized_matrix_non_alias : sx_initialize_safety_wit_66_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_67_initialized_matrix_non_alias : sx_initialize_safety_wit_67_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_68_rejected_coefficient : sx_initialize_safety_wit_68_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_69_rejected_coefficient : sx_initialize_safety_wit_69_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_70_initialized_matrix_non_alias : sx_initialize_safety_wit_70_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_71_zero_rows : sx_initialize_safety_wit_71_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_72_rejected_coefficient : sx_initialize_safety_wit_72_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_73_initialized_matrix_non_alias : sx_initialize_safety_wit_73_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_74_zero_rows : sx_initialize_safety_wit_74_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_75_zero_rows : sx_initialize_safety_wit_75_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_76_initialized_matrix_non_alias : sx_initialize_safety_wit_76_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_77_rejected_coefficient : sx_initialize_safety_wit_77_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_78_zero_rows : sx_initialize_safety_wit_78_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_79_initialized_matrix_non_alias : sx_initialize_safety_wit_79_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_80_rejected_coefficient : sx_initialize_safety_wit_80_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_81_zero_rows : sx_initialize_safety_wit_81_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_82_initialized_matrix_non_alias : sx_initialize_safety_wit_82_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_83_rejected_coefficient : sx_initialize_safety_wit_83_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_84_zero_rows : sx_initialize_safety_wit_84_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_85_initialized_matrix_non_alias : sx_initialize_safety_wit_85_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_86_rejected_coefficient : sx_initialize_safety_wit_86_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_87_zero_rows : sx_initialize_safety_wit_87_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_88_initialized_matrix_non_alias : sx_initialize_safety_wit_88_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_89_rejected_coefficient : sx_initialize_safety_wit_89_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_90_zero_rows : sx_initialize_safety_wit_90_zero_rows.
Axiom proof_of_sx_initialize_safety_wit_91_initialized_matrix_non_alias : sx_initialize_safety_wit_91_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_92_rejected_coefficient : sx_initialize_safety_wit_92_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_93_initialized_matrix_non_alias : sx_initialize_safety_wit_93_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_94_rejected_coefficient : sx_initialize_safety_wit_94_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_95_initialized_matrix_non_alias : sx_initialize_safety_wit_95_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_96_rejected_coefficient : sx_initialize_safety_wit_96_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_97_initialized_matrix_non_alias : sx_initialize_safety_wit_97_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_98_rejected_coefficient : sx_initialize_safety_wit_98_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_99_initialized_matrix_non_alias : sx_initialize_safety_wit_99_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_100_rejected_coefficient : sx_initialize_safety_wit_100_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_101_initialized_matrix_non_alias : sx_initialize_safety_wit_101_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_102_rejected_coefficient : sx_initialize_safety_wit_102_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_103_rejected_coefficient : sx_initialize_safety_wit_103_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_104_rejected_coefficient : sx_initialize_safety_wit_104_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_105_initialized_matrix_non_alias : sx_initialize_safety_wit_105_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_106_initialized_matrix_non_alias : sx_initialize_safety_wit_106_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_107_rejected_coefficient : sx_initialize_safety_wit_107_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_108_initialized_matrix_non_alias : sx_initialize_safety_wit_108_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_109_rejected_coefficient : sx_initialize_safety_wit_109_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_110_initialized_matrix_non_alias : sx_initialize_safety_wit_110_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_safety_wit_111_rejected_coefficient : sx_initialize_safety_wit_111_rejected_coefficient.
Axiom proof_of_sx_initialize_safety_wit_112_initialized_matrix_non_alias : sx_initialize_safety_wit_112_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_1_rejected_coefficient : sx_initialize_entail_wit_1_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_2_initialized_matrix_non_alias : sx_initialize_entail_wit_2_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_3_zero_rows : sx_initialize_entail_wit_3_zero_rows.
Axiom proof_of_sx_initialize_entail_wit_4_rejected_coefficient : sx_initialize_entail_wit_4_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_5_initialized_matrix_non_alias : sx_initialize_entail_wit_5_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_6_rejected_coefficient : sx_initialize_entail_wit_6_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_7_initialized_matrix_non_alias : sx_initialize_entail_wit_7_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_8_rejected_coefficient : sx_initialize_entail_wit_8_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_9_rejected_coefficient : sx_initialize_entail_wit_9_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_10_initialized_matrix_non_alias : sx_initialize_entail_wit_10_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_11_initialized_matrix_non_alias : sx_initialize_entail_wit_11_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_12_rejected_coefficient : sx_initialize_entail_wit_12_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_13_rejected_coefficient : sx_initialize_entail_wit_13_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_14_initialized_matrix_non_alias : sx_initialize_entail_wit_14_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_15_zero_rows : sx_initialize_entail_wit_15_zero_rows.
Axiom proof_of_sx_initialize_entail_wit_16_initialized_matrix_non_alias : sx_initialize_entail_wit_16_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_17_rejected_coefficient : sx_initialize_entail_wit_17_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_18_zero_rows : sx_initialize_entail_wit_18_zero_rows.
Axiom proof_of_sx_initialize_entail_wit_19_zero_rows : sx_initialize_entail_wit_19_zero_rows.
Axiom proof_of_sx_initialize_entail_wit_20_initialized_matrix_non_alias : sx_initialize_entail_wit_20_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_21_rejected_coefficient : sx_initialize_entail_wit_21_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_22_zero_rows : sx_initialize_entail_wit_22_zero_rows.
Axiom proof_of_sx_initialize_entail_wit_23_initialized_matrix_non_alias : sx_initialize_entail_wit_23_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_24_rejected_coefficient : sx_initialize_entail_wit_24_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_25_initialized_matrix_non_alias : sx_initialize_entail_wit_25_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_26_rejected_coefficient : sx_initialize_entail_wit_26_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_27_initialized_matrix_non_alias : sx_initialize_entail_wit_27_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_28_rejected_coefficient : sx_initialize_entail_wit_28_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_29_initialized_matrix_non_alias : sx_initialize_entail_wit_29_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_30_rejected_coefficient : sx_initialize_entail_wit_30_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_31_initialized_matrix_non_alias : sx_initialize_entail_wit_31_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_32_rejected_coefficient : sx_initialize_entail_wit_32_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_33_1_rejected_coefficient : sx_initialize_entail_wit_33_1_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_33_2_rejected_coefficient : sx_initialize_entail_wit_33_2_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_34_1_initialized_matrix_non_alias : sx_initialize_entail_wit_34_1_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_34_2_initialized_matrix_non_alias : sx_initialize_entail_wit_34_2_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_35_rejected_coefficient : sx_initialize_entail_wit_35_rejected_coefficient.
Axiom proof_of_sx_initialize_entail_wit_36_initialized_matrix_non_alias : sx_initialize_entail_wit_36_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_37_initialized_matrix_non_alias : sx_initialize_entail_wit_37_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_entail_wit_38_rejected_coefficient : sx_initialize_entail_wit_38_rejected_coefficient.
Axiom proof_of_sx_initialize_return_wit_1_zero_rows : sx_initialize_return_wit_1_zero_rows.
Axiom proof_of_sx_initialize_return_wit_2_initialized_matrix_non_alias : sx_initialize_return_wit_2_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_return_wit_3_rejected_coefficient : sx_initialize_return_wit_3_rejected_coefficient.
Axiom proof_of_sx_initialize_return_wit_4_initialized_matrix_non_alias : sx_initialize_return_wit_4_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_return_wit_5_rejected_coefficient : sx_initialize_return_wit_5_rejected_coefficient.
Axiom proof_of_sx_initialize_return_wit_6_invalid_dimensions : sx_initialize_return_wit_6_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_7_invalid_dimensions : sx_initialize_return_wit_7_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_8_invalid_dimensions : sx_initialize_return_wit_8_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_9_invalid_dimensions : sx_initialize_return_wit_9_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_10_invalid_dimensions : sx_initialize_return_wit_10_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_11_invalid_dimensions : sx_initialize_return_wit_11_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_12_invalid_dimensions : sx_initialize_return_wit_12_invalid_dimensions.
Axiom proof_of_sx_initialize_return_wit_13_invalid_dimensions : sx_initialize_return_wit_13_invalid_dimensions.
Axiom proof_of_sx_initialize_partial_solve_wit_1_zero_rows : sx_initialize_partial_solve_wit_1_zero_rows.
Axiom proof_of_sx_initialize_partial_solve_wit_2_initialized_matrix_non_alias : sx_initialize_partial_solve_wit_2_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_partial_solve_wit_3_rejected_coefficient : sx_initialize_partial_solve_wit_3_rejected_coefficient.
Axiom proof_of_sx_initialize_partial_solve_wit_4_zero_rows : sx_initialize_partial_solve_wit_4_zero_rows.
Axiom proof_of_sx_initialize_partial_solve_wit_5_initialized_matrix_non_alias : sx_initialize_partial_solve_wit_5_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_partial_solve_wit_6_rejected_coefficient : sx_initialize_partial_solve_wit_6_rejected_coefficient.
Axiom proof_of_sx_initialize_partial_solve_wit_7_zero_rows : sx_initialize_partial_solve_wit_7_zero_rows.
Axiom proof_of_sx_initialize_partial_solve_wit_8_initialized_matrix_non_alias : sx_initialize_partial_solve_wit_8_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_partial_solve_wit_9_rejected_coefficient : sx_initialize_partial_solve_wit_9_rejected_coefficient.
Axiom proof_of_sx_initialize_partial_solve_wit_10_rejected_coefficient : sx_initialize_partial_solve_wit_10_rejected_coefficient.
Axiom proof_of_sx_initialize_partial_solve_wit_11_initialized_matrix_non_alias : sx_initialize_partial_solve_wit_11_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_partial_solve_wit_12_zero_rows_pure : sx_initialize_partial_solve_wit_12_zero_rows_pure.
Axiom proof_of_sx_initialize_partial_solve_wit_12_zero_rows : sx_initialize_partial_solve_wit_12_zero_rows.
Axiom proof_of_sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure : sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias_pure.
Axiom proof_of_sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias : sx_initialize_partial_solve_wit_13_initialized_matrix_non_alias.
Axiom proof_of_sx_initialize_partial_solve_wit_14_rejected_coefficient_pure : sx_initialize_partial_solve_wit_14_rejected_coefficient_pure.
Axiom proof_of_sx_initialize_partial_solve_wit_14_rejected_coefficient : sx_initialize_partial_solve_wit_14_rejected_coefficient.

End VC_Correct.
