From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.build_fme_model_input_revision_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_one_sided_policy_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.violated_fme_model_selection_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.entering_fme_model_selection_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.pivot_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.pivot_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.sx_check_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.sx_check_qcp_opt_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function sx_check_qcp -----*)

Definition sx_check_qcp_safety_wit_1 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (q: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (q <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < M_rational_feasibility_normal)) (PreH8 : (coef <> 0)) (PreH9 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH10 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size coef (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) sz )
  **  (MpzArray.missing_i coef 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_check_qcp_safety_wit_2 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (q: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (q <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i < M_rational_feasibility_normal)) (PreH8 : (coef <> 0)) (PreH9 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH10 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size coef (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) sz )
  **  (MpzArray.missing_i coef 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_check_qcp_safety_wit_3 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (q: Z) (PreH1 : (sz > 0)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) )),
  ((( &( "j" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size coef (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) sz )
  **  (MpzArray.missing_i coef 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_check_qcp_safety_wit_4 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (N_rational_feasibility_normal < N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= N_rational_feasibility_normal)) (PreH13 : (N_rational_feasibility_normal <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ False ”
.

Definition sx_check_qcp_safety_wit_5 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz: Z) (j: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (j >= N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) j )) (PreH16 : (j < N_rational_feasibility_normal)) (PreH17 : (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ False ”
.

Definition sx_check_qcp_safety_wit_6 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz: Z) (j: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (j < N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) j )) (PreH16 : (j < N_rational_feasibility_normal)) (PreH17 : (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_qcp_safety_wit_7 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz: Z) (j: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (j < N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= j)) (PreH13 : (j <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) j )) (PreH16 : (j < N_rational_feasibility_normal)) (PreH17 : (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_check_qcp_safety_wit_8 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz: Z) (j: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (j = N_rational_feasibility_normal)) (PreH2 : (sz <> 0)) (PreH3 : (j < N_rational_feasibility_normal)) (PreH4 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH5 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH6 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH8 : (q <> 0)) (PreH9 : (0 <= i)) (PreH10 : (i < M_rational_feasibility_normal)) (PreH11 : (coef <> 0)) (PreH12 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH13 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH14 : (0 <= j)) (PreH15 : (j <= N_rational_feasibility_normal)) (PreH16 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH17 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) j )) (PreH18 : (j < N_rational_feasibility_normal)) (PreH19 : (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ False ”
.

Definition sx_check_qcp_safety_wit_9 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (N_rational_feasibility_normal >= N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= N_rational_feasibility_normal)) (PreH13 : (N_rational_feasibility_normal <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_qcp_safety_wit_10 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (K: Z) (P: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K = (P + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH5 : ((0 < P) -> (simplex_mpz_layout ))) (PreH6 : (selection_basis P K D A B R )) (PreH7 : (pivot_nonbasic_columns K B R NB )) (PreH8 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_qcp_safety_wit_11 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (retval = UINT_MAX)) (PreH2 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH3 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH4 : (selection_basis P K D A B R )) (PreH5 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH6 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH7 : (K = (P + N_rational_feasibility_normal ))) (PreH8 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH9 : ((0 < P) -> (simplex_mpz_layout ))) (PreH10 : (selection_basis P K D A B R )) (PreH11 : (pivot_nonbasic_columns K B R NB )) (PreH12 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sx_check_qcp_safety_wit_12 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = UINT_MAX)) (PreH2 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K) (R) ((entering_row (retval) (K) ((scan_header_sizes (AT)))))))) (PreH3 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K) (R) ((entering_row (retval) (K) ((scan_row_values (A)))))))) (PreH4 : ((retval_2 = UINT_MAX) -> (entering_blocked_row N_rational_feasibility_normal K retval A ))) (PreH5 : (selection_basis P K D A B R )) (PreH6 : (retval <> UINT_MAX)) (PreH7 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH8 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH9 : (selection_basis P K D A B R )) (PreH10 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH11 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH12 : (K = (P + N_rational_feasibility_normal ))) (PreH13 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH14 : ((0 < P) -> (simplex_mpz_layout ))) (PreH15 : (selection_basis P K D A B R )) (PreH16 : (pivot_nonbasic_columns K B R NB )) (PreH17 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "e" ) )) # UInt  |-> retval_2)
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sx_check_qcp_entail_wit_1 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  ((( &( "variables" ) )) # UInt  |-> variables_pre)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
|--
  EX (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rational_feasibility_normal) ”
  &&  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  (build_input_segment head_pre head_pre (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
|--
  EX (i: Z),
  “ (variables_pre = N_rational_feasibility_normal) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rational_feasibility_normal) ”
  &&  (build_input_segment head_pre head_pre (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
).

Definition sx_check_qcp_entail_wit_2 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (q: Z) (i_2: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= M_rational_feasibility_normal)) (PreH7 : (q <> 0)),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment q 0 (N_rational_feasibility_normal + 1 ) (sublist (i_2) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
|--
  EX (sz: Z) (next: Z) (coef: Z) (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rational_feasibility_normal) ”
  &&  “ (coef <> 0) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) ) ”
  &&  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size coef (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) sz )
  **  (MpzArray.missing_i coef 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (q: Z) (i_2: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 <= M_rational_feasibility_normal)) (PreH7 : (q <> 0)),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment q 0 (N_rational_feasibility_normal + 1 ) (sublist (i_2) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
|--
  EX (sz: Z) (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rational_feasibility_normal) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))) <> 0) ”
  &&  “ (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) ) ”
  &&  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))
  **  (build_input_segment (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))) 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&((((build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))) + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))) (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)) sz )
  **  (MpzArray.missing_i (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))) 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
).

Definition sx_check_qcp_entail_wit_3 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz_2: Z) (q: Z) (PreH1 : (sz_2 > 0)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < M_rational_feasibility_normal)) (PreH9 : (coef_2 <> 0)) (PreH10 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH11 : (next_2 = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH12 : (os_size_relation sz_2 (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)) )),
  ((( &( "j" ) )) # UInt  |-> 0)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  (build_input_segment next_2 0 (N_rational_feasibility_normal + 1 ) (sublist ((i_2 + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef_2 + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_2)
  **  (os_mpz_without_size coef_2 (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)) sz_2 )
  **  (MpzArray.missing_i coef_2 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2)))) )
|--
  (EX (next: Z) (coef: Z) (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rational_feasibility_normal) ”
  &&  “ (coef <> 0) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (0 <= N_rational_feasibility_normal) ”
  &&  “ (N_rational_feasibility_normal <= N_rational_feasibility_normal) ”
  &&  “ (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0))) ”
  &&  “ (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal ) ”
  &&  ((( &( "j" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) ))
  ||
  (EX (sz: Z) (j: Z) (next: Z) (coef: Z) (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rational_feasibility_normal) ”
  &&  “ (coef <> 0) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= N_rational_feasibility_normal) ”
  &&  “ (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0))) ”
  &&  “ (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) j ) ”
  &&  “ (j < N_rational_feasibility_normal) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) ) ”
  &&  ((( &( "j" ) )) # UInt  |-> j)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) ))
.

Definition sx_check_qcp_entail_wit_4 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz_2: Z) (j_2: Z) (next_2: Z) (coef_2: Z) (i_2: Z) (q: Z) (PreH1 : (sz_2 = 0)) (PreH2 : (j_2 < N_rational_feasibility_normal)) (PreH3 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH4 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH5 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH7 : (q <> 0)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < M_rational_feasibility_normal)) (PreH10 : (coef_2 <> 0)) (PreH11 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH12 : (next_2 = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH13 : (0 <= j_2)) (PreH14 : (j_2 <= N_rational_feasibility_normal)) (PreH15 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)))) (PreH16 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i_2)) j_2 )) (PreH17 : (j_2 < N_rational_feasibility_normal)) (PreH18 : (os_size_relation sz_2 (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i_2))) (j_2)) )),
  ((( &( "j" ) )) # UInt  |-> (j_2 + 1 ))
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  (build_input_segment next_2 0 (N_rational_feasibility_normal + 1 ) (sublist ((i_2 + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef_2 + ((j_2 + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz_2)
  **  (os_mpz_without_size (coef_2 + ((j_2 + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i_2))) (j_2)) sz_2 )
  **  (MpzArray.missing_i coef_2 (j_2 + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2)))) )
|--
  (EX (next: Z) (coef: Z) (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rational_feasibility_normal) ”
  &&  “ (coef <> 0) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (0 <= N_rational_feasibility_normal) ”
  &&  “ (N_rational_feasibility_normal <= N_rational_feasibility_normal) ”
  &&  “ (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0))) ”
  &&  “ (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal ) ”
  &&  ((( &( "j" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) ))
  ||
  (EX (sz: Z) (j: Z) (next: Z) (coef: Z) (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_rational_feasibility_normal) ”
  &&  “ (coef <> 0) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i))))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= N_rational_feasibility_normal) ”
  &&  “ (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0))) ”
  &&  “ (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) j ) ”
  &&  “ (j < N_rational_feasibility_normal) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) ) ”
  &&  ((( &( "j" ) )) # UInt  |-> j)
  **  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) ))
.

Definition sx_check_qcp_entail_wit_5_1 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz: Z) (j: Z) (next: Z) (coef: Z) (i_2: Z) (q: Z) (PreH1 : (j <> N_rational_feasibility_normal)) (PreH2 : (sz <> 0)) (PreH3 : (j < N_rational_feasibility_normal)) (PreH4 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH5 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH6 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH8 : (q <> 0)) (PreH9 : (0 <= i_2)) (PreH10 : (i_2 < M_rational_feasibility_normal)) (PreH11 : (coef <> 0)) (PreH12 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH13 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH14 : (0 <= j)) (PreH15 : (j <= N_rational_feasibility_normal)) (PreH16 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)))) (PreH17 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i_2)) j )) (PreH18 : (j < N_rational_feasibility_normal)) (PreH19 : (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i_2))) (j)) )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i_2 + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2)))) )
|--
  EX (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rational_feasibility_normal) ”
  &&  (build_input_segment head_pre next (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (sz: Z) (j: Z) (next: Z) (coef: Z) (i_2: Z) (q: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (j <> N_rational_feasibility_normal)) (PreH4 : (sz <> 0)) (PreH5 : (j < N_rational_feasibility_normal)) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH10 : (q <> 0)) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < M_rational_feasibility_normal)) (PreH13 : (coef <> 0)) (PreH14 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH15 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH16 : (0 <= j)) (PreH17 : (j <= N_rational_feasibility_normal)) (PreH18 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)))) (PreH19 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i_2)) j )) (PreH20 : (j < N_rational_feasibility_normal)) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i_2))) (j)) )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i_2 + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_rational_feasibility_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2)))) )
|--
  EX (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rational_feasibility_normal) ”
  &&  (build_input_segment head_pre next (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
).

Definition sx_check_qcp_entail_wit_5_2 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (i_2: Z) (coef: Z) (next: Z) (sz: Z) (q: Z) (PreH1 : (sz <= 0)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH12 : (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)) )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i_2 + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size coef (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)) sz )
  **  (MpzArray.missing_i coef 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2)))) )
|--
  EX (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rational_feasibility_normal) ”
  &&  (build_input_segment head_pre next (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (i_2: Z) (coef: Z) (next: Z) (sz: Z) (q: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (sz <= 0)) (PreH4 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH5 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH6 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH8 : (q <> 0)) (PreH9 : (0 <= i_2)) (PreH10 : (i_2 < M_rational_feasibility_normal)) (PreH11 : (coef <> 0)) (PreH12 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH13 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i_2)))))) (PreH14 : (os_size_relation sz (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)) )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i_2) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i_2 + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  ((&(((coef + (0 * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size coef (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2))))) (0)) sz )
  **  (MpzArray.missing_i coef 0 0 (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i_2)))) )
|--
  EX (i: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_rational_feasibility_normal) ”
  &&  (build_input_segment head_pre next (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
).

Definition sx_check_qcp_entail_wit_6 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (q: Z) (i: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (0 <= i)) (PreH6 : (i <= M_rational_feasibility_normal)) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment q 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
|--
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (q: Z) (i: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (0 <= i)) (PreH6 : (i <= M_rational_feasibility_normal)) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment q 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
|--
  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
).

Definition sx_check_qcp_entail_wit_6_split_goal_spatial :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (q: Z) (i: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH5 : (0 <= i)) (PreH6 : (i <= M_rational_feasibility_normal)) (PreH7 : (q = 0)),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  (build_input_segment q 0 (N_rational_feasibility_normal + 1 ) (sublist (i) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
|--
  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
.

Definition sx_check_qcp_entail_wit_7 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> retval_rows)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token dPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_rational_feasibility_normal nbVals )
|--
  EX (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (K: Z) (P: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  TT && emp 
|--
  “ (selection_equations N_rational_feasibility_normal retval_rows (retval_rows + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (pivot_nonbasic_columns (retval_rows + N_rational_feasibility_normal ) bVals rowVals nbVals ) ”
  &&  “ (selection_basis retval_rows (retval_rows + N_rational_feasibility_normal ) dVals aVals bVals rowVals ) ”
  &&  “ ((0 < retval_rows) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_dimensions_ok retval_rows N_rational_feasibility_normal ) ”
  &&  emp
).

Definition sx_check_qcp_entail_wit_7_split_goal_1 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (selection_equations N_rational_feasibility_normal retval_rows (retval_rows + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )
.

Definition sx_check_qcp_entail_wit_7_split_goal_2 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (pivot_nonbasic_columns (retval_rows + N_rational_feasibility_normal ) bVals rowVals nbVals )
.

Definition sx_check_qcp_entail_wit_7_split_goal_3 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (selection_basis retval_rows (retval_rows + N_rational_feasibility_normal ) dVals aVals bVals rowVals )
.

Definition sx_check_qcp_entail_wit_7_split_goal_4 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  ((0 < retval_rows) -> (simplex_mpz_layout ))
.

Definition sx_check_qcp_entail_wit_7_split_goal_5 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (simplex_dimensions_ok retval_rows N_rational_feasibility_normal )
.

Definition sx_check_qcp_entail_wit_8 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (NP_2: Z) (RP_2: Z) (BP_2: Z) (AP_2: Z) (CP_2: Z) (DP_2: Z) (C_2: (@list Z)) (NB_2: (@list Z)) (D_2: (@list Z)) (A_2: (@list Z)) (B_2: (@list Z)) (R_2: (@list Z)) (K_2: Z) (P_2: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K_2 = (P_2 + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH5 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH6 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH7 : (pivot_nonbasic_columns K_2 B_2 R_2 NB_2 )) (PreH8 : (selection_equations N_rational_feasibility_normal P_2 K_2 (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B_2 )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP_2)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 ((P_2 * K_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (K_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP_2 P_2 D_2 )
  **  (MpzArray.full CP_2 P_2 C_2 )
  **  (MpzArray.full AP_2 (P_2 * K_2 ) A_2 )
  **  (UIntArray.full BP_2 P_2 B_2 )
  **  (UIntArray.full RP_2 K_2 R_2 )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB_2 )
|--
  EX (AT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (DT: (@list scan_mpz_snapshot)) (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (K: Z) (P: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (NP_2: Z) (RP_2: Z) (BP_2: Z) (AP_2: Z) (CP_2: Z) (DP_2: Z) (C_2: (@list Z)) (NB_2: (@list Z)) (D_2: (@list Z)) (A_2: (@list Z)) (B_2: (@list Z)) (R_2: (@list Z)) (K_2: Z) (P_2: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K_2 = (P_2 + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH5 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH6 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH7 : (pivot_nonbasic_columns K_2 B_2 R_2 NB_2 )) (PreH8 : (selection_equations N_rational_feasibility_normal P_2 K_2 (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B_2 )),
  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 ((P_2 * K_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (K_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP_2 P_2 D_2 )
  **  (MpzArray.full CP_2 P_2 C_2 )
  **  (MpzArray.full AP_2 (P_2 * K_2 ) A_2 )
  **  (UIntArray.full BP_2 P_2 B_2 )
  **  (UIntArray.full RP_2 K_2 R_2 )
|--
  EX (AT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (DT: (@list scan_mpz_snapshot)) (C: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)),
  “ (K_2 = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K_2 = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) N_rational_feasibility_normal ) ”
  &&  “ ((0 < (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) D A B R ) ”
  &&  “ (pivot_nonbasic_columns ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) B R NB_2 ) ”
  &&  “ (selection_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D DT )
  **  (scan_mpz_array CP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) C CT )
  **  (scan_mpz_array AP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) A AT )
  **  (UIntArray.full BP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) B )
  **  (UIntArray.full RP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) R )
).

Definition sx_check_qcp_entail_wit_9 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K_2: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B_2: (@list Z)) (R_2: (@list Z)) (NB_2: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> UINT_MAX)) (PreH2 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K_2) (R_2) ((entering_row (retval) (K_2) ((scan_header_sizes (AT)))))))) (PreH3 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K_2) (R_2) ((entering_row (retval) (K_2) ((scan_row_values (A_2)))))))) (PreH4 : ((retval_2 = UINT_MAX) -> (entering_blocked_row N_rational_feasibility_normal K_2 retval A_2 ))) (PreH5 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH6 : (retval <> UINT_MAX)) (PreH7 : (retval = (first_positive_row (N_rational_feasibility_normal) (K_2) ((sublist (N_rational_feasibility_normal) (K_2) (R_2))) ((scan_header_sizes (CT)))))) (PreH8 : (retval = (first_positive_row (N_rational_feasibility_normal) (K_2) ((sublist (N_rational_feasibility_normal) (K_2) (R_2))) ((scan_row_values (C_2)))))) (PreH9 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH10 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH11 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH12 : (K_2 = (P_2 + N_rational_feasibility_normal ))) (PreH13 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH14 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH15 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH16 : (pivot_nonbasic_columns K_2 B_2 R_2 NB_2 )) (PreH17 : (selection_equations N_rational_feasibility_normal P_2 K_2 (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B_2 )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP_2)
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP_2 P_2 D_2 DT )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP_2 P_2 C_2 CT )
  **  (simplex_malloc_token AP_2 ((P_2 * K_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP_2 (P_2 * K_2 ) A_2 AT )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (UIntArray.full BP_2 P_2 B_2 )
  **  (simplex_malloc_token RP_2 (K_2 * sizeof(UINT) ) )
  **  (UIntArray.full RP_2 K_2 R_2 )
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP_2)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB_2 )
|--
  EX (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (K: Z) (P: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P (K - P ) ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < P) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < K) ”
  &&  “ ((Znth retval_2 R 0) = UINT_MAX) ”
  &&  “ ((pivot_coef (A) (K) (retval) (retval_2)) <> 0) ”
  &&  “ (sx_entering_slot_matches NB retval_2 ) ”
  &&  “ ((Zlength (NB)) = (K - P )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP (K - P ) NB )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K_2: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B_2: (@list Z)) (R_2: (@list Z)) (NB_2: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> UINT_MAX)) (PreH2 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K_2) (R_2) ((entering_row (retval) (K_2) ((scan_header_sizes (AT)))))))) (PreH3 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K_2) (R_2) ((entering_row (retval) (K_2) ((scan_row_values (A_2)))))))) (PreH4 : ((retval_2 = UINT_MAX) -> (entering_blocked_row N_rational_feasibility_normal K_2 retval A_2 ))) (PreH5 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH6 : (retval <> UINT_MAX)) (PreH7 : (retval = (first_positive_row (N_rational_feasibility_normal) (K_2) ((sublist (N_rational_feasibility_normal) (K_2) (R_2))) ((scan_header_sizes (CT)))))) (PreH8 : (retval = (first_positive_row (N_rational_feasibility_normal) (K_2) ((sublist (N_rational_feasibility_normal) (K_2) (R_2))) ((scan_row_values (C_2)))))) (PreH9 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH10 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH11 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH12 : (K_2 = (P_2 + N_rational_feasibility_normal ))) (PreH13 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH14 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH15 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH16 : (pivot_nonbasic_columns K_2 B_2 R_2 NB_2 )) (PreH17 : (selection_equations N_rational_feasibility_normal P_2 K_2 (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B_2 )),
  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP_2 P_2 D_2 DT )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP_2 P_2 C_2 CT )
  **  (simplex_malloc_token AP_2 ((P_2 * K_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP_2 (P_2 * K_2 ) A_2 AT )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (UIntArray.full BP_2 P_2 B_2 )
  **  (simplex_malloc_token RP_2 (K_2 * sizeof(UINT) ) )
  **  (UIntArray.full RP_2 K_2 R_2 )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB_2 )
|--
  EX (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)),
  “ (K_2 = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K_2 = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) - (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ) ) ”
  &&  “ ((0 < (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (selection_basis (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) D A B R ) ”
  &&  “ (pivot_nonbasic_columns ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ ((Znth retval_2 R 0) = UINT_MAX) ”
  &&  “ ((pivot_coef (A) (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) (retval) (retval_2)) <> 0) ”
  &&  “ (sx_entering_slot_matches NB retval_2 ) ”
  &&  “ ((Zlength (NB)) = (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) - (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) )) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D )
  **  (MpzArray.full CP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) C )
  **  (MpzArray.full AP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) A )
  **  (UIntArray.full BP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) B )
  **  (UIntArray.full RP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) R )
  **  (UIntArray.full NP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) - (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ) NB )
).

Definition sx_check_qcp_entail_wit_10 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K_2: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B_2: (@list Z)) (R_2: (@list Z)) (NB_2: (@list Z)) (r: Z) (e: Z) (Df: (@list Z)) (Cf: (@list Z)) (Af: (@list Z)) (Bf: (@list Z)) (Rf: (@list Z)) (Nf: (@list Z)) (PreH1 : (simplex_dimensions_ok P_2 (K_2 - P_2 ) )) (PreH2 : (pivot_optimized_result P_2 K_2 r e (sx_entering_slot (NB_2) (e)) D_2 C_2 A_2 B_2 R_2 NB_2 Df Cf Af Bf Rf Nf )) (PreH3 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH4 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (K_2 = (P_2 + N_rational_feasibility_normal ))) (PreH6 : (simplex_dimensions_ok P_2 (K_2 - P_2 ) )) (PreH7 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH8 : (simplex_mpz_layout )) (PreH9 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH10 : (pivot_nonbasic_columns K_2 B_2 R_2 NB_2 )) (PreH11 : (selection_equations N_rational_feasibility_normal P_2 K_2 (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B_2 )) (PreH12 : (0 <= r)) (PreH13 : (r < P_2)) (PreH14 : (0 <= e)) (PreH15 : (e < K_2)) (PreH16 : ((Znth e R_2 0) = UINT_MAX)) (PreH17 : ((pivot_coef (A_2) (K_2) (r) (e)) <> 0)) (PreH18 : (sx_entering_slot_matches NB_2 e )) (PreH19 : ((Zlength (NB_2)) = (K_2 - P_2 ))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP_2)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP_2)
  **  (MpzArray.full DP_2 P_2 Df )
  **  (MpzArray.full CP_2 P_2 Cf )
  **  (MpzArray.full AP_2 (P_2 * K_2 ) Af )
  **  (UIntArray.full BP_2 P_2 Bf )
  **  (UIntArray.full RP_2 K_2 Rf )
  **  (UIntArray.full NP_2 (K_2 - P_2 ) Nf )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 ((P_2 * K_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (K_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
|--
  EX (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (K: Z) (P: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K_2: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B_2: (@list Z)) (R_2: (@list Z)) (NB_2: (@list Z)) (r: Z) (e: Z) (Df: (@list Z)) (Cf: (@list Z)) (Af: (@list Z)) (Bf: (@list Z)) (Rf: (@list Z)) (Nf: (@list Z)) (PreH1 : (simplex_dimensions_ok P_2 (K_2 - P_2 ) )) (PreH2 : (pivot_optimized_result P_2 K_2 r e (sx_entering_slot (NB_2) (e)) D_2 C_2 A_2 B_2 R_2 NB_2 Df Cf Af Bf Rf Nf )) (PreH3 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH4 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (K_2 = (P_2 + N_rational_feasibility_normal ))) (PreH6 : (simplex_dimensions_ok P_2 (K_2 - P_2 ) )) (PreH7 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH8 : (simplex_mpz_layout )) (PreH9 : (selection_basis P_2 K_2 D_2 A_2 B_2 R_2 )) (PreH10 : (pivot_nonbasic_columns K_2 B_2 R_2 NB_2 )) (PreH11 : (selection_equations N_rational_feasibility_normal P_2 K_2 (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B_2 )) (PreH12 : (0 <= r)) (PreH13 : (r < P_2)) (PreH14 : (0 <= e)) (PreH15 : (e < K_2)) (PreH16 : ((Znth e R_2 0) = UINT_MAX)) (PreH17 : ((pivot_coef (A_2) (K_2) (r) (e)) <> 0)) (PreH18 : (sx_entering_slot_matches NB_2 e )) (PreH19 : ((Zlength (NB_2)) = (K_2 - P_2 ))),
  (MpzArray.full DP_2 P_2 Df )
  **  (MpzArray.full CP_2 P_2 Cf )
  **  (MpzArray.full AP_2 (P_2 * K_2 ) Af )
  **  (UIntArray.full BP_2 P_2 Bf )
  **  (UIntArray.full RP_2 K_2 Rf )
  **  (UIntArray.full NP_2 (K_2 - P_2 ) Nf )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 ((P_2 * K_2 ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (K_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
|--
  EX (C: (@list Z)) (NB: (@list Z)) (D: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)),
  “ (K_2 = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K_2 = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) N_rational_feasibility_normal ) ”
  &&  “ ((0 < (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) D A B R ) ”
  &&  “ (pivot_nonbasic_columns ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D )
  **  (MpzArray.full CP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) C )
  **  (MpzArray.full AP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) A )
  **  (UIntArray.full BP_2 (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) B )
  **  (UIntArray.full RP_2 ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) R )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB )
).

Definition sx_check_qcp_entail_wit_11_1 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (retval = UINT_MAX)) (PreH2 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH3 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C_2)))))) (PreH4 : (selection_basis P_2 K D_2 A_2 B R )) (PreH5 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH6 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH7 : (K = (P_2 + N_rational_feasibility_normal ))) (PreH8 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH9 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH10 : (selection_basis P_2 K D_2 A_2 B R )) (PreH11 : (pivot_nonbasic_columns K B R NB )) (PreH12 : (selection_equations N_rational_feasibility_normal P_2 K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP_2)
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP_2 P_2 D_2 DT )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP_2 P_2 C_2 CT )
  **  (simplex_malloc_token AP_2 ((P_2 * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP_2 (P_2 * K ) A_2 AT )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (UIntArray.full BP_2 P_2 B )
  **  (simplex_malloc_token RP_2 (K * sizeof(UINT) ) )
  **  (UIntArray.full RP_2 K R )
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP_2)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB )
|--
  EX (A: (@list Z)) (C: (@list Z)) (D: (@list Z)) (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (t_addr_cols: Z) (P: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 0 ) ”
  &&  “ (t_addr_cols = (P + N_rational_feasibility_normal )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * (P + N_rational_feasibility_normal ) ) A )
  **  (UCharArray.undef_full BP (P * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP (N_rational_feasibility_normal * sizeof(UINT) ) )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (retval = UINT_MAX)) (PreH2 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH3 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C_2)))))) (PreH4 : (selection_basis P_2 K D_2 A_2 B R )) (PreH5 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH6 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH7 : (K = (P_2 + N_rational_feasibility_normal ))) (PreH8 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH9 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH10 : (selection_basis P_2 K D_2 A_2 B R )) (PreH11 : (pivot_nonbasic_columns K B R NB )) (PreH12 : (selection_equations N_rational_feasibility_normal P_2 K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B )),
  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP_2 P_2 D_2 DT )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP_2 P_2 C_2 CT )
  **  (simplex_malloc_token AP_2 ((P_2 * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP_2 (P_2 * K ) A_2 AT )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (UIntArray.full BP_2 P_2 B )
  **  (simplex_malloc_token RP_2 (K * sizeof(UINT) ) )
  **  (UIntArray.full RP_2 K R )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB )
|--
  EX (A: (@list Z)) (C: (@list Z)) (D: (@list Z)),
  “ (K = (P_2 + N_rational_feasibility_normal )) ”
  &&  “ (K = (P_2 + N_rational_feasibility_normal )) ”
  &&  “ (K = (P_2 + N_rational_feasibility_normal )) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok P_2 N_rational_feasibility_normal ) ”
  &&  “ ((0 < P_2) -> (simplex_mpz_layout )) ”
  &&  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 0 ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 ((P_2 * (P_2 + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 ((P_2 + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP_2 P_2 D )
  **  (MpzArray.full CP_2 P_2 C )
  **  (MpzArray.full AP_2 (P_2 * (P_2 + N_rational_feasibility_normal ) ) A )
  **  (UCharArray.undef_full BP_2 (P_2 * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_2 ((P_2 + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
).

Definition sx_check_qcp_entail_wit_11_2 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = UINT_MAX)) (PreH2 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K) (R) ((entering_row (retval) (K) ((scan_header_sizes (AT)))))))) (PreH3 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K) (R) ((entering_row (retval) (K) ((scan_row_values (A_2)))))))) (PreH4 : ((retval_2 = UINT_MAX) -> (entering_blocked_row N_rational_feasibility_normal K retval A_2 ))) (PreH5 : (selection_basis P_2 K D_2 A_2 B R )) (PreH6 : (retval <> UINT_MAX)) (PreH7 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH8 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C_2)))))) (PreH9 : (selection_basis P_2 K D_2 A_2 B R )) (PreH10 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH11 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH12 : (K = (P_2 + N_rational_feasibility_normal ))) (PreH13 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH14 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH15 : (selection_basis P_2 K D_2 A_2 B R )) (PreH16 : (pivot_nonbasic_columns K B R NB )) (PreH17 : (selection_equations N_rational_feasibility_normal P_2 K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP_2)
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP_2 P_2 D_2 DT )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP_2 P_2 C_2 CT )
  **  (simplex_malloc_token AP_2 ((P_2 * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP_2 (P_2 * K ) A_2 AT )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (UIntArray.full BP_2 P_2 B )
  **  (simplex_malloc_token RP_2 (K * sizeof(UINT) ) )
  **  (UIntArray.full RP_2 K R )
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP_2)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB )
|--
  EX (A: (@list Z)) (C: (@list Z)) (D: (@list Z)) (NP: Z) (RP: Z) (BP: Z) (AP: Z) (CP: Z) (DP: Z) (t_addr_cols: Z) (P: Z),
  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 1 ) ”
  &&  “ (t_addr_cols = (P + N_rational_feasibility_normal )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * (P + N_rational_feasibility_normal ) ) A )
  **  (UCharArray.undef_full BP (P * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP (N_rational_feasibility_normal * sizeof(UINT) ) )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P_2: Z) (K: Z) (DP_2: Z) (CP_2: Z) (AP_2: Z) (BP_2: Z) (RP_2: Z) (NP_2: Z) (D_2: (@list Z)) (C_2: (@list Z)) (A_2: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = UINT_MAX)) (PreH2 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K) (R) ((entering_row (retval) (K) ((scan_header_sizes (AT)))))))) (PreH3 : (retval_2 = (first_entering (N_rational_feasibility_normal) (K) (R) ((entering_row (retval) (K) ((scan_row_values (A_2)))))))) (PreH4 : ((retval_2 = UINT_MAX) -> (entering_blocked_row N_rational_feasibility_normal K retval A_2 ))) (PreH5 : (selection_basis P_2 K D_2 A_2 B R )) (PreH6 : (retval <> UINT_MAX)) (PreH7 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH8 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C_2)))))) (PreH9 : (selection_basis P_2 K D_2 A_2 B R )) (PreH10 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH11 : (P_2 = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH12 : (K = (P_2 + N_rational_feasibility_normal ))) (PreH13 : (simplex_dimensions_ok P_2 N_rational_feasibility_normal )) (PreH14 : ((0 < P_2) -> (simplex_mpz_layout ))) (PreH15 : (selection_basis P_2 K D_2 A_2 B R )) (PreH16 : (pivot_nonbasic_columns K B R NB )) (PreH17 : (selection_equations N_rational_feasibility_normal P_2 K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D_2 C_2 A_2 B )),
  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP_2 P_2 D_2 DT )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP_2 P_2 C_2 CT )
  **  (simplex_malloc_token AP_2 ((P_2 * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP_2 (P_2 * K ) A_2 AT )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (UIntArray.full BP_2 P_2 B )
  **  (simplex_malloc_token RP_2 (K * sizeof(UINT) ) )
  **  (UIntArray.full RP_2 K R )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP_2 N_rational_feasibility_normal NB )
|--
  EX (A: (@list Z)) (C: (@list Z)) (D: (@list Z)),
  “ (K = (P_2 + N_rational_feasibility_normal )) ”
  &&  “ (K = (P_2 + N_rational_feasibility_normal )) ”
  &&  “ (K = (P_2 + N_rational_feasibility_normal )) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok P_2 N_rational_feasibility_normal ) ”
  &&  “ ((0 < P_2) -> (simplex_mpz_layout )) ”
  &&  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 1 ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP_2 (P_2 * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP_2 ((P_2 * (P_2 + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP_2 (P_2 * sizeof(UINT) ) )
  **  (simplex_malloc_token RP_2 ((P_2 + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP_2 P_2 D )
  **  (MpzArray.full CP_2 P_2 C )
  **  (MpzArray.full AP_2 (P_2 * (P_2 + N_rational_feasibility_normal ) ) A )
  **  (UCharArray.undef_full BP_2 (P_2 * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP_2 ((P_2 + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP_2 (N_rational_feasibility_normal * sizeof(UINT) ) )
).

Definition sx_check_qcp_return_wit_1 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (result: Z) (t_addr_cols: Z) (t_cols: Z) (PreH1 : (t_cols = (P + N_rational_feasibility_normal ))) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH4 : ((0 < P) -> (simplex_mpz_layout ))) (PreH5 : (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) result )) (PreH6 : (t_addr_cols = (P + N_rational_feasibility_normal ))),
  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
|--
  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) result ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
.

Definition sx_check_qcp_return_wit_2 :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (N_rational_feasibility_normal >= N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= N_rational_feasibility_normal)) (PreH13 : (N_rational_feasibility_normal <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 1 ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (N_rational_feasibility_normal >= N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= N_rational_feasibility_normal)) (PreH13 : (N_rational_feasibility_normal <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 1 ) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
).

Definition sx_check_qcp_return_wit_2_split_goal_1 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (N_rational_feasibility_normal >= N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= N_rational_feasibility_normal)) (PreH13 : (N_rational_feasibility_normal <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) 1 ) ”
.

Definition sx_check_qcp_return_wit_2_split_goal_spatial :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (next: Z) (coef: Z) (i: Z) (q: Z) (PreH1 : (N_rational_feasibility_normal >= N_rational_feasibility_normal)) (PreH2 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH3 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH4 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))) (PreH6 : (q <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i < M_rational_feasibility_normal)) (PreH9 : (coef <> 0)) (PreH10 : (coef = (build_row_coefficients ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH11 : (next = (build_row_next ((build_row_at (Rows_rational_feasibility_normal) (i)))))) (PreH12 : (0 <= N_rational_feasibility_normal)) (PreH13 : (N_rational_feasibility_normal <= N_rational_feasibility_normal)) (PreH14 : (0 < (Znth (0) ((build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i))))) (0)))) (PreH15 : (sx_zero_prefix (build_row_at (Rows_rational_feasibility_normal) (i)) N_rational_feasibility_normal )),
  (build_input_segment head_pre q (N_rational_feasibility_normal + 1 ) (sublist (0) (i) (Rows_rational_feasibility_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (build_input_segment next 0 (N_rational_feasibility_normal + 1 ) (sublist ((i + 1 )) (M_rational_feasibility_normal) (Rows_rational_feasibility_normal)) )
  **  (MpzArray.full coef (N_rational_feasibility_normal + 1 ) (build_row_entries ((build_row_at (Rows_rational_feasibility_normal) (i)))) )
|--
  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
.

Definition sx_check_qcp_partial_solve_wit_1_pure :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
|--
  “ (N_rational_feasibility_normal = N_rational_feasibility_normal) ”
  &&  “ ((Zlength (Rows_rational_feasibility_normal)) = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok (Zlength (Rows_rational_feasibility_normal)) N_rational_feasibility_normal ) ”
  &&  “ ((0 < (Zlength (Rows_rational_feasibility_normal))) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (Zlength (Rows_rational_feasibility_normal))) -> (os_node_layout )) ”
.

Definition sx_check_qcp_partial_solve_wit_1_aux :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH3 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH4 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  (UndefStructPredtable ( &( "t" ) ) )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
|--
  “ (N_rational_feasibility_normal = N_rational_feasibility_normal) ”
  &&  “ ((Zlength (Rows_rational_feasibility_normal)) = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok (Zlength (Rows_rational_feasibility_normal)) N_rational_feasibility_normal ) ”
  &&  “ ((0 < (Zlength (Rows_rational_feasibility_normal))) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (Zlength (Rows_rational_feasibility_normal))) -> (os_node_layout )) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (UndefStructPredtable ( &( "t" ) ) )
.

Definition sx_check_qcp_partial_solve_wit_1 := sx_check_qcp_partial_solve_wit_1_pure -> sx_check_qcp_partial_solve_wit_1_aux.

Definition sx_check_qcp_partial_solve_wit_2 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (retval: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals )) (PreH4 : (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH5 : (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ))) (PreH6 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH7 : (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal )) (PreH8 : ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_rational_feasibility_normal) -> (os_node_layout ))),
  ((&((retval)  # "table" ->ₛ "rows")) # UInt  |-> retval_rows)
  **  ((&((retval)  # "table" ->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&((retval)  # "table" ->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&((retval)  # "table" ->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&((retval)  # "table" ->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&((retval)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&((retval)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&((retval)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token dPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_rational_feasibility_normal nbVals )
  **  (UndefStructPredtable ( &( "t" ) ) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < N_rational_feasibility_normal)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (simplex_initial_table N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_rational_feasibility_normal (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (retval_rows = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (retval_cols = ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal )) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok M_rational_feasibility_normal N_rational_feasibility_normal ) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_rational_feasibility_normal) -> (os_node_layout )) ”
  &&  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |->_)
  **  ((&((retval)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |->_)
  **  ((&((retval)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |->_)
  **  ((&((retval)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |->_)
  **  ((&((retval)  # "table" ->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |->_)
  **  ((&((retval)  # "table" ->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |->_)
  **  ((&((retval)  # "table" ->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |->_)
  **  ((&((retval)  # "table" ->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |->_)
  **  ((&((retval)  # "table" ->ₛ "rows")) # UInt  |-> retval_rows)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token dPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) + N_rational_feasibility_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_rational_feasibility_normal nbVals )
.

Definition sx_check_qcp_partial_solve_wit_3_pure :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K = (P + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH5 : ((0 < P) -> (simplex_mpz_layout ))) (PreH6 : (selection_basis P K D A B R )) (PreH7 : (pivot_nonbasic_columns K B R NB )) (PreH8 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (N_rational_feasibility_normal = N_rational_feasibility_normal) ”
  &&  “ (N_rational_feasibility_normal <= K) ”
  &&  “ (K <= UINT_MAX) ”
  &&  “ (((P * K ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((K * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= P) ”
  &&  “ ((P + N_rational_feasibility_normal ) <= UINT_MAX) ”
  &&  “ (N_rational_feasibility_normal <= (P + N_rational_feasibility_normal )) ”
  &&  “ (0 <= N_rational_feasibility_normal) ”
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
).

Definition sx_check_qcp_partial_solve_wit_3_pure_split_goal_1 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_3_pure_split_goal_2 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_3_pure_split_goal_3 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_3_pure_split_goal_4 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_3_pure_split_goal_5 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_3_pure_split_goal_6 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (K <= UINT_MAX)) (PreH2 : (P <= UINT_MAX)) (PreH3 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH4 : (K >= 0)) (PreH5 : (P >= 0)) (PreH6 : (N_rational_feasibility_normal >= 0)) (PreH7 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH8 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH9 : (K = (P + N_rational_feasibility_normal ))) (PreH10 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH11 : ((0 < P) -> (simplex_mpz_layout ))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (pivot_nonbasic_columns K B R NB )) (PreH14 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_3_aux :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K = (P + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH5 : ((0 < P) -> (simplex_mpz_layout ))) (PreH6 : (selection_basis P K D A B R )) (PreH7 : (pivot_nonbasic_columns K B R NB )) (PreH8 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (scan_mpz_array DP P D DT )
  **  (scan_mpz_array CP P C CT )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (N_rational_feasibility_normal = N_rational_feasibility_normal) ”
  &&  “ (N_rational_feasibility_normal <= K) ”
  &&  “ (K <= UINT_MAX) ”
  &&  “ (((P * K ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((K * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (0 <= P) ”
  &&  “ ((P + N_rational_feasibility_normal ) <= UINT_MAX) ”
  &&  “ (N_rational_feasibility_normal <= (P + N_rational_feasibility_normal )) ”
  &&  “ (0 <= N_rational_feasibility_normal) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
.

Definition sx_check_qcp_partial_solve_wit_3 := sx_check_qcp_partial_solve_wit_3_pure -> sx_check_qcp_partial_solve_wit_3_aux.

Definition sx_check_qcp_partial_solve_wit_4_pure :=
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (retval <> UINT_MAX)) (PreH2 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH3 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH4 : (selection_basis P K D A B R )) (PreH5 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH6 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH7 : (K = (P + N_rational_feasibility_normal ))) (PreH8 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH9 : ((0 < P) -> (simplex_mpz_layout ))) (PreH10 : (selection_basis P K D A B R )) (PreH11 : (pivot_nonbasic_columns K B R NB )) (PreH12 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (N_rational_feasibility_normal = N_rational_feasibility_normal) ”
  &&  “ (retval = retval) ”
  &&  “ (N_rational_feasibility_normal <= K) ”
  &&  “ (0 < K) ”
  &&  “ (K <= UINT_MAX) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < P) ”
  &&  “ (((P * K ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((K * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT)))) < P) ”
  &&  “ (0 <= (first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT))))) ”
  &&  “ ((P + N_rational_feasibility_normal ) <= UINT_MAX) ”
  &&  “ (0 < (P + N_rational_feasibility_normal )) ”
  &&  “ (N_rational_feasibility_normal <= (P + N_rational_feasibility_normal )) ”
  &&  “ (0 <= N_rational_feasibility_normal) ”
) \/
(
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (0 < (P + N_rational_feasibility_normal )) ”
  &&  “ (0 <= (first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT))))) ”
  &&  “ ((first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT)))) < P) ”
  &&  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ (retval < P) ”
  &&  “ (0 < (P + N_rational_feasibility_normal )) ”
).

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_1 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (0 < (P + N_rational_feasibility_normal )) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_2 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (0 <= (first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT))))) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_3 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ ((first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT)))) < P) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_4 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_5 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_6 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_7 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_8 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (simplex_mpz_layout ) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_9 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_10 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_11 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (retval < P) ”
.

Definition sx_check_qcp_partial_solve_wit_4_pure_split_goal_12 :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (N_rational_feasibility_normal <= UINT_MAX)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : (K <= UINT_MAX)) (PreH4 : (P <= UINT_MAX)) (PreH5 : (N_rational_feasibility_normal >= 0)) (PreH6 : (retval >= 0)) (PreH7 : (K >= 0)) (PreH8 : (P >= 0)) (PreH9 : (retval <> UINT_MAX)) (PreH10 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH11 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH12 : (selection_basis P K D A B R )) (PreH13 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH14 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH15 : (K = (P + N_rational_feasibility_normal ))) (PreH16 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH17 : ((0 < P) -> (simplex_mpz_layout ))) (PreH18 : (selection_basis P K D A B R )) (PreH19 : (pivot_nonbasic_columns K B R NB )) (PreH20 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((( &( "e" ) )) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((( &( "r" ) )) # UInt  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (0 < (P + N_rational_feasibility_normal )) ”
.

Definition sx_check_qcp_partial_solve_wit_4_aux :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (DT: (@list scan_mpz_snapshot)) (CT: (@list scan_mpz_snapshot)) (AT: (@list scan_mpz_snapshot)) (retval: Z) (PreH1 : (retval <> UINT_MAX)) (PreH2 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT)))))) (PreH3 : (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C)))))) (PreH4 : (selection_basis P K D A B R )) (PreH5 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH6 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH7 : (K = (P + N_rational_feasibility_normal ))) (PreH8 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH9 : ((0 < P) -> (simplex_mpz_layout ))) (PreH10 : (selection_basis P K D A B R )) (PreH11 : (pivot_nonbasic_columns K B R NB )) (PreH12 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
|--
  “ (N_rational_feasibility_normal = N_rational_feasibility_normal) ”
  &&  “ (retval = retval) ”
  &&  “ (N_rational_feasibility_normal <= K) ”
  &&  “ (0 < K) ”
  &&  “ (K <= UINT_MAX) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < P) ”
  &&  “ (((P * K ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((K * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (((P + N_rational_feasibility_normal ) * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ ((P * sizeof(UINT) ) <= INT_MAX) ”
  &&  “ (((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((P * sizeof( "__mpz_struct" ) ) <= INT_MAX) ”
  &&  “ ((first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT)))) < P) ”
  &&  “ (0 <= (first_positive_row (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) ((sublist (N_rational_feasibility_normal) ((P + N_rational_feasibility_normal )) (R))) ((scan_header_sizes (CT))))) ”
  &&  “ ((P + N_rational_feasibility_normal ) <= UINT_MAX) ”
  &&  “ (0 < (P + N_rational_feasibility_normal )) ”
  &&  “ (N_rational_feasibility_normal <= (P + N_rational_feasibility_normal )) ”
  &&  “ (0 <= N_rational_feasibility_normal) ”
  &&  “ (retval <> UINT_MAX) ”
  &&  “ (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_header_sizes (CT))))) ”
  &&  “ (retval = (first_positive_row (N_rational_feasibility_normal) (K) ((sublist (N_rational_feasibility_normal) (K) (R))) ((scan_row_values (C))))) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array DP P D DT )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array CP P C CT )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (scan_mpz_array AP (P * K ) A AT )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UIntArray.full BP P B )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (UIntArray.full RP K R )
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UIntArray.full NP N_rational_feasibility_normal NB )
.

Definition sx_check_qcp_partial_solve_wit_4 := sx_check_qcp_partial_solve_wit_4_pure -> sx_check_qcp_partial_solve_wit_4_aux.

Definition sx_check_qcp_partial_solve_wit_5_pure :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (r: Z) (e: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K = (P + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P (K - P ) )) (PreH5 : ((0 < P) -> (simplex_mpz_layout ))) (PreH6 : (simplex_mpz_layout )) (PreH7 : (selection_basis P K D A B R )) (PreH8 : (pivot_nonbasic_columns K B R NB )) (PreH9 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )) (PreH10 : (0 <= r)) (PreH11 : (r < P)) (PreH12 : (0 <= e)) (PreH13 : (e < K)) (PreH14 : ((Znth e R 0) = UINT_MAX)) (PreH15 : ((pivot_coef (A) (K) (r) (e)) <> 0)) (PreH16 : (sx_entering_slot_matches NB e )) (PreH17 : ((Zlength (NB)) = (K - P ))),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "r" ) )) # UInt  |-> r)
  **  ((( &( "e" ) )) # UInt  |-> e)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  ((( &( "result" ) )) # Int  |->_)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP (K - P ) NB )
|--
  “ (simplex_dimensions_ok P (K - P ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= r) ”
  &&  “ (r < P) ”
  &&  “ (0 <= e) ”
  &&  “ (e < K) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ ((Znth e R 0) = UINT_MAX) ”
  &&  “ ((pivot_coef (A) (K) (r) (e)) <> 0) ”
  &&  “ (sx_entering_slot_matches NB e ) ”
  &&  “ ((Zlength (NB)) = (K - P )) ”
  &&  “ (r = r) ”
  &&  “ (e = e) ”
.

Definition sx_check_qcp_partial_solve_wit_5_aux :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (K: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (B: (@list Z)) (R: (@list Z)) (NB: (@list Z)) (r: Z) (e: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))))) (PreH3 : (K = (P + N_rational_feasibility_normal ))) (PreH4 : (simplex_dimensions_ok P (K - P ) )) (PreH5 : ((0 < P) -> (simplex_mpz_layout ))) (PreH6 : (simplex_mpz_layout )) (PreH7 : (selection_basis P K D A B R )) (PreH8 : (pivot_nonbasic_columns K B R NB )) (PreH9 : (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B )) (PreH10 : (0 <= r)) (PreH11 : (r < P)) (PreH12 : (0 <= e)) (PreH13 : (e < K)) (PreH14 : ((Znth e R 0) = UINT_MAX)) (PreH15 : ((pivot_coef (A) (K) (r) (e)) <> 0)) (PreH16 : (sx_entering_slot_matches NB e )) (PreH17 : ((Zlength (NB)) = (K - P ))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP (K - P ) NB )
|--
  “ (simplex_dimensions_ok P (K - P ) ) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (0 <= r) ”
  &&  “ (r < P) ”
  &&  “ (0 <= e) ”
  &&  “ (e < K) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ ((Znth e R 0) = UINT_MAX) ”
  &&  “ ((pivot_coef (A) (K) (r) (e)) <> 0) ”
  &&  “ (sx_entering_slot_matches NB e ) ”
  &&  “ ((Zlength (NB)) = (K - P )) ”
  &&  “ (r = r) ”
  &&  “ (e = e) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (P = (Zlength ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal))))) ”
  &&  “ (K = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P (K - P ) ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_mpz_layout ) ”
  &&  “ (selection_basis P K D A B R ) ”
  &&  “ (pivot_nonbasic_columns K B R NB ) ”
  &&  “ (selection_equations N_rational_feasibility_normal P K (build_matrix ((os_kept (N_rational_feasibility_normal) (Rows_rational_feasibility_normal)))) D C A B ) ”
  &&  “ (0 <= r) ”
  &&  “ (r < P) ”
  &&  “ (0 <= e) ”
  &&  “ (e < K) ”
  &&  “ ((Znth e R 0) = UINT_MAX) ”
  &&  “ ((pivot_coef (A) (K) (r) (e)) <> 0) ”
  &&  “ (sx_entering_slot_matches NB e ) ”
  &&  “ ((Zlength (NB)) = (K - P )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> K)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * K ) A )
  **  (UIntArray.full BP P B )
  **  (UIntArray.full RP K R )
  **  (UIntArray.full NP (K - P ) NB )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * K ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP (K * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
.

Definition sx_check_qcp_partial_solve_wit_5 := sx_check_qcp_partial_solve_wit_5_pure -> sx_check_qcp_partial_solve_wit_5_aux.

Definition sx_check_qcp_partial_solve_wit_6_pure :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (result: Z) (t_addr_cols: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH3 : ((0 < P) -> (simplex_mpz_layout ))) (PreH4 : (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) result )) (PreH5 : (t_addr_cols = (P + N_rational_feasibility_normal ))),
  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_rational_feasibility_normal)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * (P + N_rational_feasibility_normal ) ) A )
  **  (UCharArray.undef_full BP (P * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP (N_rational_feasibility_normal * sizeof(UINT) ) )
|--
  “ ((P + N_rational_feasibility_normal ) = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
.

Definition sx_check_qcp_partial_solve_wit_6_aux :=
forall (Rows_rational_feasibility_normal: (@list build_row_snapshot)) (M_rational_feasibility_normal: Z) (N_rational_feasibility_normal: Z) (head_pre: Z) (P: Z) (DP: Z) (CP: Z) (AP: Z) (BP: Z) (RP: Z) (NP: Z) (D: (@list Z)) (C: (@list Z)) (A: (@list Z)) (result: Z) (t_addr_cols: Z) (PreH1 : (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal)))) (PreH2 : (simplex_dimensions_ok P N_rational_feasibility_normal )) (PreH3 : ((0 < P) -> (simplex_mpz_layout ))) (PreH4 : (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) result )) (PreH5 : (t_addr_cols = (P + N_rational_feasibility_normal ))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token AP ((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (MpzArray.full DP P D )
  **  (MpzArray.full CP P C )
  **  (MpzArray.full AP (P * (P + N_rational_feasibility_normal ) ) A )
  **  (UCharArray.undef_full BP (P * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP (N_rational_feasibility_normal * sizeof(UINT) ) )
|--
  “ ((P + N_rational_feasibility_normal ) = (P + N_rational_feasibility_normal )) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (M_rational_feasibility_normal = (Zlength (Rows_rational_feasibility_normal))) ”
  &&  “ (simplex_dimensions_ok P N_rational_feasibility_normal ) ”
  &&  “ ((0 < P) -> (simplex_mpz_layout )) ”
  &&  “ (sx_check_result N_rational_feasibility_normal M_rational_feasibility_normal (build_matrix (Rows_rational_feasibility_normal)) result ) ”
  &&  “ (t_addr_cols = (P + N_rational_feasibility_normal )) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> P)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> (P + N_rational_feasibility_normal ))
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> DP)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> CP)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> AP)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> BP)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> RP)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> NP)
  **  (simplex_malloc_token DP (P * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full DP P D )
  **  (simplex_malloc_token CP (P * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full CP P C )
  **  (simplex_malloc_token AP ((P * (P + N_rational_feasibility_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full AP (P * (P + N_rational_feasibility_normal ) ) A )
  **  (simplex_malloc_token BP (P * sizeof(UINT) ) )
  **  (UCharArray.undef_full BP (P * sizeof(UINT) ) )
  **  (simplex_malloc_token RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (UCharArray.undef_full RP ((P + N_rational_feasibility_normal ) * sizeof(UINT) ) )
  **  (simplex_malloc_token NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (UCharArray.undef_full NP (N_rational_feasibility_normal * sizeof(UINT) ) )
  **  (build_input_segment head_pre 0 (N_rational_feasibility_normal + 1 ) Rows_rational_feasibility_normal )
.

Definition sx_check_qcp_partial_solve_wit_6 := sx_check_qcp_partial_solve_wit_6_pure -> sx_check_qcp_partial_solve_wit_6_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_sx_check_qcp_safety_wit_1 : sx_check_qcp_safety_wit_1.
Axiom proof_of_sx_check_qcp_safety_wit_2 : sx_check_qcp_safety_wit_2.
Axiom proof_of_sx_check_qcp_safety_wit_3 : sx_check_qcp_safety_wit_3.
Axiom proof_of_sx_check_qcp_safety_wit_4 : sx_check_qcp_safety_wit_4.
Axiom proof_of_sx_check_qcp_safety_wit_5 : sx_check_qcp_safety_wit_5.
Axiom proof_of_sx_check_qcp_safety_wit_6 : sx_check_qcp_safety_wit_6.
Axiom proof_of_sx_check_qcp_safety_wit_7 : sx_check_qcp_safety_wit_7.
Axiom proof_of_sx_check_qcp_safety_wit_8 : sx_check_qcp_safety_wit_8.
Axiom proof_of_sx_check_qcp_safety_wit_9 : sx_check_qcp_safety_wit_9.
Axiom proof_of_sx_check_qcp_safety_wit_10 : sx_check_qcp_safety_wit_10.
Axiom proof_of_sx_check_qcp_safety_wit_11 : sx_check_qcp_safety_wit_11.
Axiom proof_of_sx_check_qcp_safety_wit_12 : sx_check_qcp_safety_wit_12.
Axiom proof_of_sx_check_qcp_entail_wit_1 : sx_check_qcp_entail_wit_1.
Axiom proof_of_sx_check_qcp_entail_wit_2 : sx_check_qcp_entail_wit_2.
Axiom proof_of_sx_check_qcp_entail_wit_3 : sx_check_qcp_entail_wit_3.
Axiom proof_of_sx_check_qcp_entail_wit_4 : sx_check_qcp_entail_wit_4.
Axiom proof_of_sx_check_qcp_entail_wit_5_1 : sx_check_qcp_entail_wit_5_1.
Axiom proof_of_sx_check_qcp_entail_wit_5_2 : sx_check_qcp_entail_wit_5_2.
Axiom proof_of_sx_check_qcp_entail_wit_6 : sx_check_qcp_entail_wit_6.
Axiom proof_of_sx_check_qcp_entail_wit_7 : sx_check_qcp_entail_wit_7.
Axiom proof_of_sx_check_qcp_entail_wit_8 : sx_check_qcp_entail_wit_8.
Axiom proof_of_sx_check_qcp_entail_wit_9 : sx_check_qcp_entail_wit_9.
Axiom proof_of_sx_check_qcp_entail_wit_10 : sx_check_qcp_entail_wit_10.
Axiom proof_of_sx_check_qcp_entail_wit_11_1 : sx_check_qcp_entail_wit_11_1.
Axiom proof_of_sx_check_qcp_entail_wit_11_2 : sx_check_qcp_entail_wit_11_2.
Axiom proof_of_sx_check_qcp_return_wit_1 : sx_check_qcp_return_wit_1.
Axiom proof_of_sx_check_qcp_return_wit_2 : sx_check_qcp_return_wit_2.
Axiom proof_of_sx_check_qcp_partial_solve_wit_1_pure : sx_check_qcp_partial_solve_wit_1_pure.
Axiom proof_of_sx_check_qcp_partial_solve_wit_1 : sx_check_qcp_partial_solve_wit_1.
Axiom proof_of_sx_check_qcp_partial_solve_wit_2 : sx_check_qcp_partial_solve_wit_2.
Axiom proof_of_sx_check_qcp_partial_solve_wit_3_pure : sx_check_qcp_partial_solve_wit_3_pure.
Axiom proof_of_sx_check_qcp_partial_solve_wit_3 : sx_check_qcp_partial_solve_wit_3.
Axiom proof_of_sx_check_qcp_partial_solve_wit_4_pure : sx_check_qcp_partial_solve_wit_4_pure.
Axiom proof_of_sx_check_qcp_partial_solve_wit_4 : sx_check_qcp_partial_solve_wit_4.
Axiom proof_of_sx_check_qcp_partial_solve_wit_5_pure : sx_check_qcp_partial_solve_wit_5_pure.
Axiom proof_of_sx_check_qcp_partial_solve_wit_5 : sx_check_qcp_partial_solve_wit_5.
Axiom proof_of_sx_check_qcp_partial_solve_wit_6_pure : sx_check_qcp_partial_solve_wit_6_pure.
Axiom proof_of_sx_check_qcp_partial_solve_wit_6 : sx_check_qcp_partial_solve_wit_6.

End VC_Correct.
