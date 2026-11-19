From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.gmp.minigmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.gmp.fme.fme_gmp_lib.
Local Open Scope monad.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.integers_fme_model_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_minimal.build_fme_model_input_revision_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_opt_lib.
Require Import SimpleC.EE.Applications_human.simplex_gmp_optimized.build_one_sided_policy_opt_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.gmp.minigmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import fme_gmp_strategy_proof.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_goal.
From SimpleC.EE.Applications_human.gmp.fme Require Import safeexec_fme_gmp_strategy_proof.

(*----- Function build_one_sided -----*)

Definition build_one_sided_safety_wit_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < N_stable_one_sided_build_normal) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + ((N_stable_one_sided_build_normal + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)),
  ((( &( "rows" ) )) # UInt  |->_)
  **  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (UCharArray.full retval N_stable_one_sided_build_normal (os_zeros (N_stable_one_sided_build_normal)) )
  **  ((( &( "signs" ) )) # Ptr  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks )) (PreH12 : (q <> 0)),
  ((( &( "j" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> (unsigned_last_nbits ((rows + 1 )) (32)))
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_3 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (rows = (i + 1 ))) (PreH10 : (0 <= i)) (PreH11 : (i < M_stable_one_sided_build_normal)) (PreH12 : (q <> 0)) (PreH13 : (0 <= j)) (PreH14 : (j < N_stable_one_sided_build_normal)) (PreH15 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH16 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef <> 0)) (PreH18 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH19 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  ((( &( "sign" ) )) # Int  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_one_sided_safety_wit_4 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (rows = (i + 1 ))) (PreH10 : (0 <= i)) (PreH11 : (i < M_stable_one_sided_build_normal)) (PreH12 : (q <> 0)) (PreH13 : (0 <= j)) (PreH14 : (j < N_stable_one_sided_build_normal)) (PreH15 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH16 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef <> 0)) (PreH18 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH19 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  ((( &( "sign" ) )) # Int  |-> sz)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_5 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz > 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j < N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH20 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "sign" ) )) # Int  |-> sz)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_one_sided_safety_wit_6 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz > 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j < N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH20 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal (replace_Znth (j) ((Z.lor (unsigned_last_nbits ((Znth j Masks 0)) (8)) 1)) (Masks)) )
  **  ((( &( "sign" ) )) # Int  |-> sz)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_7 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j < N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH20 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  ((( &( "sign" ) )) # Int  |-> sz)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_8 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz < 0)) (PreH2 : (sz > 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal (replace_Znth (j) ((Z.lor (unsigned_last_nbits ((Znth j Masks 0)) (8)) 1)) (Masks)) )
  **  ((( &( "sign" ) )) # Int  |-> sz)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ False ”
.

Definition build_one_sided_safety_wit_9 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz < 0)) (PreH2 : (sz <= 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "sign" ) )) # Int  |-> sz)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> rows)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_one_sided_safety_wit_10 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (signs: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + (((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) ))) (PreH13 : ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX)) (PreH14 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )),
  ((( &( "kept" ) )) # UInt  |->_)
  **  (simplex_malloc_token retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  ((( &( "nodes" ) )) # Ptr  |-> retval)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_11 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks: (@list Z)) (NodesAlign: Z) (nodes: Z) (kept: Z) (i: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= i)) (PreH10 : (i <= M_stable_one_sided_build_normal)) (PreH11 : (0 <= kept)) (PreH12 : (kept <= i)) (PreH13 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH19 : (q <> 0)),
  ((( &( "j" ) )) # UInt  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_12 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (0 <= i)) (PreH2 : (i < M_stable_one_sided_build_normal)) (PreH3 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH13 : (0 <= nodes)) (PreH14 : (nodes <= UINT_MAX)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (0 <= kept)) (PreH20 : (kept <= i)) (PreH21 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH22 : (q <> 0)) (PreH23 : (0 <= j)) (PreH24 : (j < N_stable_one_sided_build_normal)) (PreH25 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH26 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_one_sided_safety_wit_13 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks 0) <> 1)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (0 <= j)) (PreH25 : (j < N_stable_one_sided_build_normal)) (PreH26 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH27 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (2 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_one_sided_safety_wit_14 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks 0) = 1)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (0 <= j)) (PreH25 : (j < N_stable_one_sided_build_normal)) (PreH26 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH27 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_one_sided_safety_wit_15 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks 0) = 2)) (PreH2 : ((Znth j Masks 0) <> 1)) (PreH3 : (0 <= i)) (PreH4 : (i < M_stable_one_sided_build_normal)) (PreH5 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH20 : (coef <> 0)) (PreH21 : (0 <= kept)) (PreH22 : (kept <= i)) (PreH23 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH24 : (q <> 0)) (PreH25 : (0 <= j)) (PreH26 : (j < N_stable_one_sided_build_normal)) (PreH27 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH28 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_one_sided_safety_wit_16 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks 0) = 2)) (PreH2 : ((Znth j Masks 0) <> 1)) (PreH3 : (0 <= i)) (PreH4 : (i < M_stable_one_sided_build_normal)) (PreH5 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH20 : (coef <> 0)) (PreH21 : (0 <= kept)) (PreH22 : (kept <= i)) (PreH23 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH24 : (q <> 0)) (PreH25 : (0 <= j)) (PreH26 : (j < N_stable_one_sided_build_normal)) (PreH27 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH28 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_17 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks 0) = 1)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (0 <= j)) (PreH25 : (j < N_stable_one_sided_build_normal)) (PreH26 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH27 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_18 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (j: Z) (q: Z) (kept: Z) (coef: Z) (next: Z) (NodesAlign: Z) (nodes: Z) (Masks: (@list Z)) (i: Z) (PreH1 : (j <> N_stable_one_sided_build_normal)) (PreH2 : (j >= N_stable_one_sided_build_normal)) (PreH3 : (0 <= i)) (PreH4 : (i < M_stable_one_sided_build_normal)) (PreH5 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH20 : (coef <> 0)) (PreH21 : (0 <= kept)) (PreH22 : (kept <= i)) (PreH23 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH24 : (q <> 0)) (PreH25 : (0 <= j)) (PreH26 : (j <= N_stable_one_sided_build_normal)) (PreH27 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ False ”
.

Definition build_one_sided_safety_wit_19 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (j = N_stable_one_sided_build_normal)) (PreH2 : (sz <> 0)) (PreH3 : ((Znth j Masks 0) = 1)) (PreH4 : (0 <= i)) (PreH5 : (i < M_stable_one_sided_build_normal)) (PreH6 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH7 : (N_stable_one_sided_build_normal = variables_pre)) (PreH8 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH9 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH12 : (0 <= N_stable_one_sided_build_normal)) (PreH13 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH14 : (sizeof(UCHAR) = 1)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH16 : (0 <= nodes)) (PreH17 : (nodes <= UINT_MAX)) (PreH18 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH19 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH20 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH21 : (coef <> 0)) (PreH22 : (0 <= kept)) (PreH23 : (kept <= i)) (PreH24 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH25 : (q <> 0)) (PreH26 : (0 <= j)) (PreH27 : (j < N_stable_one_sided_build_normal)) (PreH28 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH29 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ False ”
.

Definition build_one_sided_safety_wit_20 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (j = N_stable_one_sided_build_normal)) (PreH2 : (sz <> 0)) (PreH3 : ((Znth j Masks 0) = 2)) (PreH4 : ((Znth j Masks 0) <> 1)) (PreH5 : (0 <= i)) (PreH6 : (i < M_stable_one_sided_build_normal)) (PreH7 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH17 : (0 <= nodes)) (PreH18 : (nodes <= UINT_MAX)) (PreH19 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH20 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH21 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH22 : (coef <> 0)) (PreH23 : (0 <= kept)) (PreH24 : (kept <= i)) (PreH25 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH26 : (q <> 0)) (PreH27 : (0 <= j)) (PreH28 : (j < N_stable_one_sided_build_normal)) (PreH29 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH30 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> j)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ False ”
.

Definition build_one_sided_safety_wit_21 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (0 <= i)) (PreH2 : (i < M_stable_one_sided_build_normal)) (PreH3 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH13 : (0 <= nodes)) (PreH14 : (nodes <= UINT_MAX)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (0 <= kept)) (PreH20 : (kept <= i)) (PreH21 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH22 : (q <> 0)) (PreH23 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH24 : (kept = 0)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |->_)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_22 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (0 <= i)) (PreH2 : (i < M_stable_one_sided_build_normal)) (PreH3 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH13 : (0 <= nodes)) (PreH14 : (nodes <= UINT_MAX)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (0 <= kept)) (PreH20 : (kept <= i)) (PreH21 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH22 : (q <> 0)) (PreH23 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH24 : (0 < kept)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |->_)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_23 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (0 <= i)) (PreH2 : (i < M_stable_one_sided_build_normal)) (PreH3 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH13 : (0 <= nodes)) (PreH14 : (nodes <= UINT_MAX)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (0 <= kept)) (PreH20 : (kept <= i)) (PreH21 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH22 : (q <> 0)) (PreH23 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH24 : (kept = 0)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_24 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (0 <= i)) (PreH2 : (i < M_stable_one_sided_build_normal)) (PreH3 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH13 : (0 <= nodes)) (PreH14 : (nodes <= UINT_MAX)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (0 <= kept)) (PreH20 : (kept <= i)) (PreH21 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH22 : (q <> 0)) (PreH23 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH24 : (0 < kept)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_25 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH25 : (kept = 0)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  “ False ”
.

Definition build_one_sided_safety_wit_26 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept = 0)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH25 : (0 < kept)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
|--
  “ False ”
.

Definition build_one_sided_safety_wit_27 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal )) (PreH25 : (0 < kept)),
  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "q" ) )) # Ptr  |-> q)
  **  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_one_sided_safety_wit_28 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <> 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ False ”
.

Definition build_one_sided_safety_wit_29 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept = 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_one_sided_safety_wit_30 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept = 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (0 < kept)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ False ”
.

Definition build_one_sided_entail_wit_1 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_stable_one_sided_build_normal)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))),
  ((( &( "variables" ) )) # UInt  |-> variables_pre)
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_stable_one_sided_build_normal)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))),
  TT && emp 
|--
  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  emp
).

Definition build_one_sided_entail_wit_1_split_goal_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_stable_one_sided_build_normal)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))),
  (N_stable_one_sided_build_normal <= INT_MAX)
.

Definition build_one_sided_entail_wit_1_split_goal_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (variables_pre: Z) (PreH1 : (variables_pre = N_stable_one_sided_build_normal)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))),
  (0 <= N_stable_one_sided_build_normal)
.

Definition build_one_sided_entail_wit_2 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < N_stable_one_sided_build_normal) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + ((N_stable_one_sided_build_normal + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)),
  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (UCharArray.full retval N_stable_one_sided_build_normal (os_zeros (N_stable_one_sided_build_normal)) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  EX (Masks: (@list Z)),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal 0 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (UCharArray.full retval N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre head_pre (N_stable_one_sided_build_normal + 1 ) (sublist (0) (0) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) (sublist (0) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < N_stable_one_sided_build_normal) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + ((N_stable_one_sided_build_normal + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)),
  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (os_masks_at N_stable_one_sided_build_normal 0 0 Rows_stable_one_sided_build_normal (os_zeros (N_stable_one_sided_build_normal)) ) ”
  &&  “ (0 <= M_stable_one_sided_build_normal) ”
  &&  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre head_pre (N_stable_one_sided_build_normal + 1 ) (sublist (0) (0) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) (sublist (0) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_2_split_goal_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < N_stable_one_sided_build_normal) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + ((N_stable_one_sided_build_normal + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)),
  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (os_masks_at N_stable_one_sided_build_normal 0 0 Rows_stable_one_sided_build_normal (os_zeros (N_stable_one_sided_build_normal)) ) ”
.

Definition build_one_sided_entail_wit_2_split_goal_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < N_stable_one_sided_build_normal) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + ((N_stable_one_sided_build_normal + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)),
  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (0 <= M_stable_one_sided_build_normal) ”
.

Definition build_one_sided_entail_wit_2_split_goal_spatial :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < N_stable_one_sided_build_normal) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + ((N_stable_one_sided_build_normal + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)),
  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  (simplex_malloc_token retval N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre head_pre (N_stable_one_sided_build_normal + 1 ) (sublist (0) (0) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) (sublist (0) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_entail_wit_3 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q <> 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)) (coef: Z) (next: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((unsigned_last_nbits ((rows + 1 )) (32)) = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q <> 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((unsigned_last_nbits ((rows + 1 )) (32)) = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_4 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (Masks_2: (@list Z)) (coef_2: Z) (next_2: Z) (j: Z) (q: Z) (i_2: Z) (rows: Z) (PreH1 : (j < N_stable_one_sided_build_normal)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i_2 + 1 ))) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j <= N_stable_one_sided_build_normal)) (PreH16 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH17 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  (MpzArray.full coef_2 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (sz: Z) (Masks: (@list Z)) (coef: Z) (next: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (Masks_2: (@list Z)) (coef_2: Z) (next_2: Z) (j: Z) (q: Z) (i_2: Z) (rows: Z) (PreH1 : (j < N_stable_one_sided_build_normal)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i_2 + 1 ))) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j <= N_stable_one_sided_build_normal)) (PreH16 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH17 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full coef_2 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (sz: Z) (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_5_1 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz: Z) (Masks_2: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz < 0)) (PreH2 : (sz <= 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i_2 + 1 ))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal (replace_Znth (j) ((Z.lor (unsigned_last_nbits ((Znth j Masks_2 0)) (8)) 2)) (Masks_2)) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)) (coef: Z) (next: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i (j + 1 ) Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz: Z) (Masks_2: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (sz < 0)) (PreH4 : (sz <= 0)) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : (rows = (i_2 + 1 ))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 < M_stable_one_sided_build_normal)) (PreH16 : (q <> 0)) (PreH17 : (0 <= j)) (PreH18 : (j < N_stable_one_sided_build_normal)) (PreH19 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef_2 <> 0)) (PreH22 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )) (PreH23 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i (j + 1 ) Rows_stable_one_sided_build_normal (replace_Znth (j) ((Z.lor (unsigned_last_nbits ((Znth j Masks_2 0)) (8)) 2)) (Masks_2)) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_5_2 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz: Z) (Masks_2: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz >= 0)) (PreH2 : (sz > 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i_2 + 1 ))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal (replace_Znth (j) ((Z.lor (unsigned_last_nbits ((Znth j Masks_2 0)) (8)) 1)) (Masks_2)) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)) (coef: Z) (next: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i (j + 1 ) Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz: Z) (Masks_2: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (sz >= 0)) (PreH4 : (sz > 0)) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : (rows = (i_2 + 1 ))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 < M_stable_one_sided_build_normal)) (PreH16 : (q <> 0)) (PreH17 : (0 <= j)) (PreH18 : (j < N_stable_one_sided_build_normal)) (PreH19 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef_2 <> 0)) (PreH22 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )) (PreH23 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i (j + 1 ) Rows_stable_one_sided_build_normal (replace_Znth (j) ((Z.lor (unsigned_last_nbits ((Znth j Masks_2 0)) (8)) 1)) (Masks_2)) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_5_3 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz: Z) (Masks_2: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz >= 0)) (PreH2 : (sz <= 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i_2 + 1 ))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)) (coef: Z) (next: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i (j + 1 ) Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (coef_2: Z) (next_2: Z) (sz: Z) (Masks_2: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (sz >= 0)) (PreH4 : (sz <= 0)) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : (rows = (i_2 + 1 ))) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 < M_stable_one_sided_build_normal)) (PreH16 : (q <> 0)) (PreH17 : (0 <= j)) (PreH18 : (j < N_stable_one_sided_build_normal)) (PreH19 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef_2 <> 0)) (PreH22 : (os_masks_at N_stable_one_sided_build_normal i_2 j Rows_stable_one_sided_build_normal Masks_2 )) (PreH23 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i (j + 1 ) Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_6 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (Masks_2: (@list Z)) (coef: Z) (next: Z) (j: Z) (q: Z) (i: Z) (rows: Z) (PreH1 : (j >= N_stable_one_sided_build_normal)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j <= N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= rows) ”
  &&  “ (rows <= M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (Masks_2: (@list Z)) (coef: Z) (next: Z) (j: Z) (q: Z) (i: Z) (rows: Z) (PreH1 : (j >= N_stable_one_sided_build_normal)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j <= N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (os_masks_at N_stable_one_sided_build_normal (i + 1 ) 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_6_split_goal_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (Masks_2: (@list Z)) (coef: Z) (next: Z) (j: Z) (q: Z) (i: Z) (rows: Z) (PreH1 : (j >= N_stable_one_sided_build_normal)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j <= N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (os_masks_at N_stable_one_sided_build_normal (i + 1 ) 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
.

Definition build_one_sided_entail_wit_6_split_goal_spatial :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (Masks_2: (@list Z)) (coef: Z) (next: Z) (j: Z) (q: Z) (i: Z) (rows: Z) (PreH1 : (j >= N_stable_one_sided_build_normal)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j <= N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_entail_wit_7 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q = 0)),
  ((( &( "rows" ) )) # UInt  |-> rows)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) ”
  &&  “ ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX) ”
  &&  “ (rows = M_stable_one_sided_build_normal) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
).

Definition build_one_sided_entail_wit_7_split_goal_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
.

Definition build_one_sided_entail_wit_7_split_goal_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX) ”
.

Definition build_one_sided_entail_wit_7_split_goal_3 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (rows = M_stable_one_sided_build_normal) ”
.

Definition build_one_sided_entail_wit_7_split_goal_spatial :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (rows: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= rows)) (PreH10 : (rows <= M_stable_one_sided_build_normal)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal rows 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH12 : (q = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (rows) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (rows) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
.

Definition build_one_sided_entail_wit_8 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks_2: (@list Z)) (signs: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + (((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) ))) (PreH13 : ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX)) (PreH14 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  EX (Masks: (@list Z)) (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= i) ”
  &&  “ (0 = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < retval) /\ (retval = (4 * NodesAlign )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((retval + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (retval) (0)) 0 (os_shadows (retval) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg retval (0 * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre head_pre (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks_2: (@list Z)) (signs: Z) (align4: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= UINT_MAX)) (PreH3 : ((0 < (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) -> (((0 < retval) /\ (retval = (4 * align4 ))) /\ ((retval + (((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) + (-1) ) * 1)) <= UINT_MAX)))) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) ))) (PreH13 : ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX)) (PreH14 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )),
  (simplex_malloc_token retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= i) ”
  &&  “ (0 = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < retval) /\ (retval = (4 * NodesAlign )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((retval + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token retval (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (retval) (0)) 0 (os_shadows (retval) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg retval (0 * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre head_pre (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_9 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (NodesAlign_2: Z) (nodes: Z) (kept: Z) (i_2: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= i_2)) (PreH10 : (i_2 <= M_stable_one_sided_build_normal)) (PreH11 : (0 <= kept)) (PreH12 : (kept <= i_2)) (PreH13 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH19 : (q <> 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i_2) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) 0 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (NodesAlign_2: Z) (nodes: Z) (kept: Z) (i_2: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= i_2)) (PreH10 : (i_2 <= M_stable_one_sided_build_normal)) (PreH11 : (0 <= kept)) (PreH12 : (kept <= i_2)) (PreH13 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH19 : (q <> 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i_2) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) 0 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_10 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (j: Z) (q: Z) (kept: Z) (coef_2: Z) (next_2: Z) (NodesAlign_2: Z) (nodes: Z) (Masks_2: (@list Z)) (i_2: Z) (PreH1 : (j < N_stable_one_sided_build_normal)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i_2)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (0 <= j)) (PreH25 : (j <= N_stable_one_sided_build_normal)) (PreH26 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  (MpzArray.full coef_2 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (sz: Z) (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (j: Z) (q: Z) (kept: Z) (coef_2: Z) (next_2: Z) (NodesAlign_2: Z) (nodes: Z) (Masks_2: (@list Z)) (i_2: Z) (PreH1 : (j < N_stable_one_sided_build_normal)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i_2)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (0 <= j)) (PreH25 : (j <= N_stable_one_sided_build_normal)) (PreH26 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full coef_2 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (sz: Z) (NodesAlign: Z) (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_11_1 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef_2: Z) (next_2: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks_2 0) <> 2)) (PreH2 : ((Znth j Masks_2 0) <> 1)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < M_stable_one_sided_build_normal)) (PreH5 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 <> 0)) (PreH21 : (0 <= kept)) (PreH22 : (kept <= i_2)) (PreH23 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH24 : (q <> 0)) (PreH25 : (0 <= j)) (PreH26 : (j < N_stable_one_sided_build_normal)) (PreH27 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH28 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) (j + 1 ) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef_2: Z) (next_2: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : ((Znth j Masks_2 0) <> 2)) (PreH4 : ((Znth j Masks_2 0) <> 1)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < M_stable_one_sided_build_normal)) (PreH7 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH17 : (0 <= nodes)) (PreH18 : (nodes <= UINT_MAX)) (PreH19 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH20 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH22 : (coef_2 <> 0)) (PreH23 : (0 <= kept)) (PreH24 : (kept <= i_2)) (PreH25 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH26 : (q <> 0)) (PreH27 : (0 <= j)) (PreH28 : (j < N_stable_one_sided_build_normal)) (PreH29 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH30 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) (j + 1 ) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_11_2 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef_2: Z) (next_2: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz = 0)) (PreH2 : ((Znth j Masks_2 0) = 1)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < M_stable_one_sided_build_normal)) (PreH5 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 <> 0)) (PreH21 : (0 <= kept)) (PreH22 : (kept <= i_2)) (PreH23 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH24 : (q <> 0)) (PreH25 : (0 <= j)) (PreH26 : (j < N_stable_one_sided_build_normal)) (PreH27 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH28 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) (j + 1 ) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef_2: Z) (next_2: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (sz = 0)) (PreH4 : ((Znth j Masks_2 0) = 1)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < M_stable_one_sided_build_normal)) (PreH7 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH17 : (0 <= nodes)) (PreH18 : (nodes <= UINT_MAX)) (PreH19 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH20 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH22 : (coef_2 <> 0)) (PreH23 : (0 <= kept)) (PreH24 : (kept <= i_2)) (PreH25 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH26 : (q <> 0)) (PreH27 : (0 <= j)) (PreH28 : (j < N_stable_one_sided_build_normal)) (PreH29 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH30 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) (j + 1 ) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_11_3 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef_2: Z) (next_2: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz = 0)) (PreH2 : ((Znth j Masks_2 0) = 2)) (PreH3 : ((Znth j Masks_2 0) <> 1)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < M_stable_one_sided_build_normal)) (PreH6 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH7 : (N_stable_one_sided_build_normal = variables_pre)) (PreH8 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH9 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH12 : (0 <= N_stable_one_sided_build_normal)) (PreH13 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH14 : (sizeof(UCHAR) = 1)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH16 : (0 <= nodes)) (PreH17 : (nodes <= UINT_MAX)) (PreH18 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH19 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef_2 <> 0)) (PreH22 : (0 <= kept)) (PreH23 : (kept <= i_2)) (PreH24 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH25 : (q <> 0)) (PreH26 : (0 <= j)) (PreH27 : (j < N_stable_one_sided_build_normal)) (PreH28 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH29 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) (j + 1 ) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef_2: Z) (next_2: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (sz = 0)) (PreH4 : ((Znth j Masks_2 0) = 2)) (PreH5 : ((Znth j Masks_2 0) <> 1)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < M_stable_one_sided_build_normal)) (PreH8 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH9 : (N_stable_one_sided_build_normal = variables_pre)) (PreH10 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH11 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH14 : (0 <= N_stable_one_sided_build_normal)) (PreH15 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH16 : (sizeof(UCHAR) = 1)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH18 : (0 <= nodes)) (PreH19 : (nodes <= UINT_MAX)) (PreH20 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH21 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH22 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH23 : (coef_2 <> 0)) (PreH24 : (0 <= kept)) (PreH25 : (kept <= i_2)) (PreH26 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH27 : (q <> 0)) (PreH28 : (0 <= j)) (PreH29 : (j < N_stable_one_sided_build_normal)) (PreH30 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH31 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef_2 + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef_2 (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ ((build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) (j + 1 ) ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (MpzArray.full (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_12 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (signs: Z) (j: Z) (q: Z) (kept: Z) (coef_2: Z) (next_2: Z) (NodesAlign_2: Z) (nodes: Z) (Masks_2: (@list Z)) (i_2: Z) (PreH1 : (j = N_stable_one_sided_build_normal)) (PreH2 : (j >= N_stable_one_sided_build_normal)) (PreH3 : (0 <= i_2)) (PreH4 : (i_2 < M_stable_one_sided_build_normal)) (PreH5 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (next_2 = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef_2 = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef_2 <> 0)) (PreH21 : (0 <= kept)) (PreH22 : (kept <= i_2)) (PreH23 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH24 : (q <> 0)) (PreH25 : (0 <= j)) (PreH26 : (j <= N_stable_one_sided_build_normal)) (PreH27 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )),
  ((( &( "j" ) )) # UInt  |-> j)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next_2)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef_2)
  **  (MpzArray.full coef_2 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next_2 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  (EX (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal ) ”
  &&  “ (kept = 0) ”
  &&  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |->_)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |->_)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) ))
  ||
  (EX (coef: Z) (next: Z) (NodesAlign: Z) (Masks: (@list Z)) (i: Z),
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) N_stable_one_sided_build_normal ) ”
  &&  “ (0 < kept) ”
  &&  ((( &( "j" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |->_)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |->_)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0))
.

Definition build_one_sided_entail_wit_13_1 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept <> 0)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i_2)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) N_stable_one_sided_build_normal )) (PreH25 : (0 < kept)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> (nodes + (kept * sizeof( "InequList" ))))
|--
  EX (Masks: (@list Z)) (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= (kept + 1 )) ”
  &&  “ ((kept + 1 ) <= i) ”
  &&  “ ((kept + 1 ) = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) ((kept + 1 ))) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept <> 0)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i_2)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) N_stable_one_sided_build_normal )) (PreH25 : (0 < kept)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (os_links nodes (nodes + ((kept - 1 ) * sizeof( "InequList" ))) (sublist (0) ((kept - 1 )) ((os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) )
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> (build_row_coefficients ((build_row_at ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal))) ((kept - 1 ))))))
  **  ((&(((nodes + ((kept - 1 ) * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> (nodes + (kept * sizeof( "InequList" ))))
|--
  EX (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= (kept + 1 )) ”
  &&  “ ((kept + 1 ) <= i) ”
  &&  “ ((kept + 1 ) = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) ((kept + 1 ))) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_13_2 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept = 0)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i_2)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) N_stable_one_sided_build_normal )) (PreH25 : (kept = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  EX (Masks: (@list Z)) (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= (kept + 1 )) ”
  &&  “ ((kept + 1 ) <= i) ”
  &&  “ ((kept + 1 ) = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) ((kept + 1 ))) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes ((kept + 1 ) * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (nodes: Z) (kept: Z) (q: Z) (signs: Z) (PreH1 : (kept = 0)) (PreH2 : (0 <= i_2)) (PreH3 : (i_2 < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i_2)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) N_stable_one_sided_build_normal )) (PreH25 : (kept = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  (MpzArray.full coef (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((nodes + (kept * sizeof( "InequList" ))))  # "InequList" ->ₛ "next")) # Ptr  |-> 0)
|--
  EX (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= (kept + 1 )) ”
  &&  “ ((kept + 1 ) <= i) ”
  &&  “ ((kept + 1 ) = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) ((kept + 1 ))) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_13_3 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (j <> N_stable_one_sided_build_normal)) (PreH2 : (sz <> 0)) (PreH3 : ((Znth j Masks_2 0) = 1)) (PreH4 : (0 <= i_2)) (PreH5 : (i_2 < M_stable_one_sided_build_normal)) (PreH6 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH7 : (N_stable_one_sided_build_normal = variables_pre)) (PreH8 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH9 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH12 : (0 <= N_stable_one_sided_build_normal)) (PreH13 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH14 : (sizeof(UCHAR) = 1)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH16 : (0 <= nodes)) (PreH17 : (nodes <= UINT_MAX)) (PreH18 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH19 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH20 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef <> 0)) (PreH22 : (0 <= kept)) (PreH23 : (kept <= i_2)) (PreH24 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH25 : (q <> 0)) (PreH26 : (0 <= j)) (PreH27 : (j < N_stable_one_sided_build_normal)) (PreH28 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH29 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)) (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (j <> N_stable_one_sided_build_normal)) (PreH4 : (sz <> 0)) (PreH5 : ((Znth j Masks_2 0) = 1)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < M_stable_one_sided_build_normal)) (PreH8 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH9 : (N_stable_one_sided_build_normal = variables_pre)) (PreH10 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH11 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH14 : (0 <= N_stable_one_sided_build_normal)) (PreH15 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH16 : (sizeof(UCHAR) = 1)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH18 : (0 <= nodes)) (PreH19 : (nodes <= UINT_MAX)) (PreH20 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH21 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH22 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH23 : (coef <> 0)) (PreH24 : (0 <= kept)) (PreH25 : (kept <= i_2)) (PreH26 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH27 : (q <> 0)) (PreH28 : (0 <= j)) (PreH29 : (j < N_stable_one_sided_build_normal)) (PreH30 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH31 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_13_4 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (j <> N_stable_one_sided_build_normal)) (PreH2 : (sz <> 0)) (PreH3 : ((Znth j Masks_2 0) = 2)) (PreH4 : ((Znth j Masks_2 0) <> 1)) (PreH5 : (0 <= i_2)) (PreH6 : (i_2 < M_stable_one_sided_build_normal)) (PreH7 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH17 : (0 <= nodes)) (PreH18 : (nodes <= UINT_MAX)) (PreH19 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH20 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH21 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH22 : (coef <> 0)) (PreH23 : (0 <= kept)) (PreH24 : (kept <= i_2)) (PreH25 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH26 : (q <> 0)) (PreH27 : (0 <= j)) (PreH28 : (j < N_stable_one_sided_build_normal)) (PreH29 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH30 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (Masks: (@list Z)) (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i_2: Z) (NodesAlign_2: Z) (coef: Z) (next: Z) (Masks_2: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz <= INT_MAX)) (PreH2 : (sz >= INT_MIN)) (PreH3 : (j <> N_stable_one_sided_build_normal)) (PreH4 : (sz <> 0)) (PreH5 : ((Znth j Masks_2 0) = 2)) (PreH6 : ((Znth j Masks_2 0) <> 1)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < M_stable_one_sided_build_normal)) (PreH9 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH10 : (N_stable_one_sided_build_normal = variables_pre)) (PreH11 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH12 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH15 : (0 <= N_stable_one_sided_build_normal)) (PreH16 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH17 : (sizeof(UCHAR) = 1)) (PreH18 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign_2 ))))) (PreH19 : (0 <= nodes)) (PreH20 : (nodes <= UINT_MAX)) (PreH21 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH22 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH23 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))))) (PreH24 : (coef <> 0)) (PreH25 : (0 <= kept)) (PreH26 : (kept <= i_2)) (PreH27 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))))) (PreH28 : (q <> 0)) (PreH29 : (0 <= j)) (PreH30 : (j < N_stable_one_sided_build_normal)) (PreH31 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i_2)) j )) (PreH32 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i_2) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i_2) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i_2))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i_2)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i_2 + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  EX (NodesAlign: Z) (i: Z),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= M_stable_one_sided_build_normal) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (build_input_segment head_pre next (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
).

Definition build_one_sided_entail_wit_14 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (q: Z) (signs: Z) (Masks_2: (@list Z)) (NodesAlign: Z) (nodes: Z) (kept: Z) (i: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= i)) (PreH10 : (i <= M_stable_one_sided_build_normal)) (PreH11 : (0 <= kept)) (PreH12 : (kept <= i)) (PreH13 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH14 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH15 : (0 <= nodes)) (PreH16 : (nodes <= UINT_MAX)) (PreH17 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH18 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks_2 )) (PreH19 : (q = 0)),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks_2 )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  (build_input_segment q 0 (N_stable_one_sided_build_normal + 1 ) (sublist (i) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  (EX (Masks: (@list Z)),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= M_stable_one_sided_build_normal) ”
  &&  “ (simplex_dimensions_ok kept N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < kept) -> (simplex_mpz_layout )) ”
  &&  “ (kept = 0) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) ))
  ||
  (EX (Masks: (@list Z)),
  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= M_stable_one_sided_build_normal) ”
  &&  “ (simplex_dimensions_ok kept N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < kept) -> (simplex_mpz_layout )) ”
  &&  “ (0 < kept) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) ))
.

Definition build_one_sided_entail_wit_15_1 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (retval_cols: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (nbVals_2: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals_2) (0)) = j))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 )) (PreH4 : (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ))) (PreH5 : (kept <> 0)) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH15 : (0 <= kept)) (PreH16 : (kept <= M_stable_one_sided_build_normal)) (PreH17 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH18 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH19 : (0 < kept)),
  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))))
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 )
  **  (simplex_malloc_token cPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals_2 )
  **  (simplex_malloc_token aPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals_2 )
  **  (simplex_malloc_token bPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals_2 )
  **  (simplex_malloc_token rowPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals_2 )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_stable_one_sided_build_normal nbVals_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  EX (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (t_addr_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)),
  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (t_addr_rows = kept) ”
  &&  “ (t_addr_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (retval_cols: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (nbVals_2: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals_2) (0)) = j))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 )) (PreH4 : (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ))) (PreH5 : (kept <> 0)) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH15 : (0 <= kept)) (PreH16 : (kept <= M_stable_one_sided_build_normal)) (PreH17 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH18 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH19 : (0 < kept)),
  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 )
  **  (simplex_malloc_token cPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals_2 )
  **  (simplex_malloc_token aPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals_2 )
  **  (simplex_malloc_token bPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals_2 )
  **  (simplex_malloc_token rowPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals_2 )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)),
  “ (retval_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = kept) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = kept) ”
  &&  “ (retval_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals_2) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  (simplex_malloc_token dPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 kept dVals )
  **  (simplex_malloc_token cPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 kept cVals )
  **  (simplex_malloc_token aPtr_2 ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr_2 (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 kept bVals )
  **  (simplex_malloc_token rowPtr_2 ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
).

Definition build_one_sided_entail_wit_15_2 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (retval_cols: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (nbVals_2: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals_2) (0)) = j))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 )) (PreH4 : (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ))) (PreH5 : (kept = 0)) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH15 : (0 <= kept)) (PreH16 : (kept <= M_stable_one_sided_build_normal)) (PreH17 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH18 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH19 : (kept = 0)),
  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))))
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 )
  **  (simplex_malloc_token cPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals_2 )
  **  (simplex_malloc_token aPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals_2 )
  **  (simplex_malloc_token bPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals_2 )
  **  (simplex_malloc_token rowPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals_2 )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_stable_one_sided_build_normal nbVals_2 )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  EX (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (t_addr_cols: Z) (t_addr_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)),
  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (t_addr_rows = kept) ”
  &&  “ (t_addr_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (nbPtr_2: Z) (rowPtr_2: Z) (bPtr_2: Z) (aPtr_2: Z) (cPtr_2: Z) (dPtr_2: Z) (retval_cols: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (nbVals_2: (@list Z)) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals_2) (0)) = j))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 cVals_2 aVals_2 bVals_2 )) (PreH4 : (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ))) (PreH5 : (kept = 0)) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH15 : (0 <= kept)) (PreH16 : (kept <= M_stable_one_sided_build_normal)) (PreH17 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH18 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH19 : (kept = 0)),
  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals_2 )
  **  (simplex_malloc_token cPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals_2 )
  **  (simplex_malloc_token aPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals_2 )
  **  (simplex_malloc_token bPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals_2 )
  **  (simplex_malloc_token rowPtr_2 (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals_2 )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (rowVals: (@list Z)),
  “ (retval_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = kept) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = kept) ”
  &&  “ (retval_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals_2) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals (@nil Z) rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals (@nil Z) ) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  (simplex_malloc_token dPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 kept dVals )
  **  (simplex_malloc_token cPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 kept cVals )
  **  (simplex_malloc_token aPtr_2 ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr_2 (kept * sizeof(UINT) ) )
  **  (simplex_malloc_token rowPtr_2 ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
).

Definition build_one_sided_return_wit_1 :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (nbVals_2: (@list Z)) (kept: Z) (t_addr_rows: Z) (t_addr_cols: Z) (record_return: Z) (PreH1 : forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals_2) (0)) = k))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals_2 cVals_2 aVals_2 bVals_2 )) (PreH4 : (t_addr_rows = kept)) (PreH5 : (t_addr_cols = (kept + N_stable_one_sided_build_normal ))) (PreH6 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))),
  ((&((record_return)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "a")) # Ptr  |-> aPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "c")) # Ptr  |-> cPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "d")) # Ptr  |-> dPtr_2)
  **  ((&((record_return)  # "table" ->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&((record_return)  # "table" ->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  (simplex_malloc_token dPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 kept dVals_2 )
  **  (simplex_malloc_token cPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 kept cVals_2 )
  **  (simplex_malloc_token aPtr_2 ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 (kept * (kept + N_stable_one_sided_build_normal ) ) aVals_2 )
  **  (simplex_malloc_token bPtr_2 (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 kept bVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 (kept + N_stable_one_sided_build_normal ) rowVals_2 )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr_2 N_stable_one_sided_build_normal nbVals_2 )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  EX (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (retval_cols: Z) (retval_rows: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)),
  “ forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (retval_rows = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (retval_cols = ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal )) ”
  &&  ((&((record_return)  # "table" ->ₛ "rows")) # UInt  |-> retval_rows)
  **  ((&((record_return)  # "table" ->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&((record_return)  # "table" ->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&((record_return)  # "table" ->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&((record_return)  # "table" ->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&((record_return)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&((record_return)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&((record_return)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token dPtr ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (dPtr_2: Z) (cPtr_2: Z) (aPtr_2: Z) (bPtr_2: Z) (rowPtr_2: Z) (nbPtr_2: Z) (dVals_2: (@list Z)) (cVals_2: (@list Z)) (aVals_2: (@list Z)) (bVals_2: (@list Z)) (rowVals_2: (@list Z)) (nbVals_2: (@list Z)) (kept: Z) (t_addr_rows: Z) (t_addr_cols: Z) (PreH1 : forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals_2) (0)) = k))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals_2 cVals_2 aVals_2 bVals_2 rowVals_2 )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals_2 cVals_2 aVals_2 bVals_2 )) (PreH4 : (t_addr_rows = kept)) (PreH5 : (t_addr_cols = (kept + N_stable_one_sided_build_normal ))) (PreH6 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))),
  (simplex_malloc_token dPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 kept dVals_2 )
  **  (simplex_malloc_token cPtr_2 (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 kept cVals_2 )
  **  (simplex_malloc_token aPtr_2 ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 (kept * (kept + N_stable_one_sided_build_normal ) ) aVals_2 )
  **  (simplex_malloc_token bPtr_2 (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 kept bVals_2 )
  **  (simplex_malloc_token rowPtr_2 ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 (kept + N_stable_one_sided_build_normal ) rowVals_2 )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  EX (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)),
  “ (t_addr_cols = ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal )) ”
  &&  “ (t_addr_rows = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (t_addr_rows = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (t_addr_cols = ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal )) ”
  &&  “ forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals_2) (0)) = j)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token dPtr_2 ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr_2 (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals )
  **  (simplex_malloc_token cPtr_2 ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr_2 (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) cVals )
  **  (simplex_malloc_token aPtr_2 (((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr_2 ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr_2 ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr_2 (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) bVals )
  **  (simplex_malloc_token rowPtr_2 (((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr_2 ((Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr_2 (N_stable_one_sided_build_normal * sizeof(UINT) ) )
).

Definition build_one_sided_partial_solve_wit_1_pure :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)),
  ((( &( "signs" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
.

Definition build_one_sided_partial_solve_wit_1_aux :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)),
  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
.

Definition build_one_sided_partial_solve_wit_1 := build_one_sided_partial_solve_wit_1_pure -> build_one_sided_partial_solve_wit_1_aux.

Definition build_one_sided_partial_solve_wit_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz > 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j < N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH20 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (sz > 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (((signs + (j * sizeof(UCHAR)))) # UChar  |-> (Znth j Masks 0))
  **  (UCharArray.missing_i signs j 0 N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_partial_solve_wit_3 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz > 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (rows = (i + 1 ))) (PreH11 : (0 <= i)) (PreH12 : (i < M_stable_one_sided_build_normal)) (PreH13 : (q <> 0)) (PreH14 : (0 <= j)) (PreH15 : (j < N_stable_one_sided_build_normal)) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH20 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (sz > 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (((signs + (j * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i signs j 0 N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_partial_solve_wit_4 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz < 0)) (PreH2 : (sz <= 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (sz < 0) ”
  &&  “ (sz <= 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (((signs + (j * sizeof(UCHAR)))) # UChar  |-> (Znth j Masks 0))
  **  (UCharArray.missing_i signs j 0 N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_partial_solve_wit_5 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (coef: Z) (next: Z) (sz: Z) (Masks: (@list Z)) (rows: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (sz < 0)) (PreH2 : (sz <= 0)) (PreH3 : (N_stable_one_sided_build_normal = variables_pre)) (PreH4 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH5 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH8 : (0 <= N_stable_one_sided_build_normal)) (PreH9 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH10 : (sizeof(UCHAR) = 1)) (PreH11 : (rows = (i + 1 ))) (PreH12 : (0 <= i)) (PreH13 : (i < M_stable_one_sided_build_normal)) (PreH14 : (q <> 0)) (PreH15 : (0 <= j)) (PreH16 : (j < N_stable_one_sided_build_normal)) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks )) (PreH21 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (sz < 0) ”
  &&  “ (sz <= 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (rows = (i + 1 )) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal i j Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (((signs + (j * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i signs j 0 N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_partial_solve_wit_6_pure :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (signs: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) ))) (PreH10 : ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )),
  ((( &( "nodes" ) )) # Ptr  |->_)
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) ”
  &&  “ ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX) ”
.

Definition build_one_sided_partial_solve_wit_6_aux :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (signs: Z) (PreH1 : (N_stable_one_sided_build_normal = variables_pre)) (PreH2 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH3 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH4 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH6 : (0 <= N_stable_one_sided_build_normal)) (PreH7 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH8 : (sizeof(UCHAR) = 1)) (PreH9 : (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) ))) (PreH10 : ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX)) (PreH11 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) ”
  &&  “ ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (0 <= (M_stable_one_sided_build_normal * sizeof( "InequList" ) )) ”
  &&  “ ((M_stable_one_sided_build_normal * sizeof( "InequList" ) ) <= INT_MAX) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
.

Definition build_one_sided_partial_solve_wit_6 := build_one_sided_partial_solve_wit_6_pure -> build_one_sided_partial_solve_wit_6_aux.

Definition build_one_sided_partial_solve_wit_7 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : (0 <= i)) (PreH2 : (i < M_stable_one_sided_build_normal)) (PreH3 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH4 : (N_stable_one_sided_build_normal = variables_pre)) (PreH5 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH6 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH7 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH9 : (0 <= N_stable_one_sided_build_normal)) (PreH10 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH11 : (sizeof(UCHAR) = 1)) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH13 : (0 <= nodes)) (PreH14 : (nodes <= UINT_MAX)) (PreH15 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH16 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH17 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef <> 0)) (PreH19 : (0 <= kept)) (PreH20 : (kept <= i)) (PreH21 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH22 : (q <> 0)) (PreH23 : (0 <= j)) (PreH24 : (j < N_stable_one_sided_build_normal)) (PreH25 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH26 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (((signs + (j * sizeof(UCHAR)))) # UChar  |-> (Znth j Masks 0))
  **  (UCharArray.missing_i signs j 0 N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_partial_solve_wit_8 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (i: Z) (NodesAlign: Z) (coef: Z) (next: Z) (Masks: (@list Z)) (sz: Z) (nodes: Z) (kept: Z) (q: Z) (j: Z) (signs: Z) (PreH1 : ((Znth j Masks 0) <> 1)) (PreH2 : (0 <= i)) (PreH3 : (i < M_stable_one_sided_build_normal)) (PreH4 : (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks )) (PreH5 : (N_stable_one_sided_build_normal = variables_pre)) (PreH6 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH7 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH8 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH10 : (0 <= N_stable_one_sided_build_normal)) (PreH11 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH12 : (sizeof(UCHAR) = 1)) (PreH13 : ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign ))))) (PreH14 : (0 <= nodes)) (PreH15 : (nodes <= UINT_MAX)) (PreH16 : ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX))) (PreH17 : (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH18 : (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i)))))) (PreH19 : (coef <> 0)) (PreH20 : (0 <= kept)) (PreH21 : (kept <= i)) (PreH22 : (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))))) (PreH23 : (q <> 0)) (PreH24 : (0 <= j)) (PreH25 : (j < N_stable_one_sided_build_normal)) (PreH26 : (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j )) (PreH27 : (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) )),
  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
|--
  “ ((Znth j Masks 0) <> 1) ”
  &&  “ (0 <= i) ”
  &&  “ (i < M_stable_one_sided_build_normal) ”
  &&  “ (os_masks_at N_stable_one_sided_build_normal M_stable_one_sided_build_normal 0 Rows_stable_one_sided_build_normal Masks ) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((0 < nodes) /\ (nodes = (4 * NodesAlign )))) ”
  &&  “ (0 <= nodes) ”
  &&  “ (nodes <= UINT_MAX) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> ((nodes + ((M_stable_one_sided_build_normal + (-1) ) * sizeof( "InequList" ))) <= UINT_MAX)) ”
  &&  “ (next = (build_row_next ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef = (build_row_coefficients ((build_row_at (Rows_stable_one_sided_build_normal) (i))))) ”
  &&  “ (coef <> 0) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= i) ”
  &&  “ (kept = (Zlength ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (q <> 0) ”
  &&  “ (0 <= j) ”
  &&  “ (j < N_stable_one_sided_build_normal) ”
  &&  “ (os_checked_prefix Rows_stable_one_sided_build_normal (build_row_at (Rows_stable_one_sided_build_normal) (i)) j ) ”
  &&  “ (os_size_relation sz (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) ) ”
  &&  (((signs + (j * sizeof(UCHAR)))) # UChar  |-> (Znth j Masks 0))
  **  (UCharArray.missing_i signs j 0 N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_links (os_temp_head (nodes) (kept)) 0 (os_shadows (nodes) (0) ((os_kept_prefix (N_stable_one_sided_build_normal) (i) (Rows_stable_one_sided_build_normal)))) )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment head_pre q (N_stable_one_sided_build_normal + 1 ) (sublist (0) (i) (Rows_stable_one_sided_build_normal)) )
  **  ((&((q)  # "InequList" ->ₛ "next")) # Ptr  |-> next)
  **  ((&((q)  # "InequList" ->ₛ "coef")) # Ptr  |-> coef)
  **  ((&(((coef + ((j + 1 ) * sizeof( "__mpz_struct" ))))  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> sz)
  **  (os_mpz_without_size (coef + ((j + 1 ) * sizeof( "__mpz_struct" ))) (os_coef ((build_row_at (Rows_stable_one_sided_build_normal) (i))) (j)) sz )
  **  (MpzArray.missing_i coef (j + 1 ) 0 (N_stable_one_sided_build_normal + 1 ) (build_row_entries ((build_row_at (Rows_stable_one_sided_build_normal) (i)))) )
  **  (build_input_segment next 0 (N_stable_one_sided_build_normal + 1 ) (sublist ((i + 1 )) (M_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)) )
.

Definition build_one_sided_partial_solve_wit_9_pure :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept = 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (N_stable_one_sided_build_normal = N_stable_one_sided_build_normal) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept = 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
).

Definition build_one_sided_partial_solve_wit_9_pure_split_goal_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept = 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
.

Definition build_one_sided_partial_solve_wit_9_pure_split_goal_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept = 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
.

Definition build_one_sided_partial_solve_wit_9_pure_split_goal_3 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept = 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
.

Definition build_one_sided_partial_solve_wit_9_pure_split_goal_4 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept = 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
.

Definition build_one_sided_partial_solve_wit_9_aux :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept = 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (kept = 0)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (N_stable_one_sided_build_normal = N_stable_one_sided_build_normal) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ (kept = 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= M_stable_one_sided_build_normal) ”
  &&  “ (simplex_dimensions_ok kept N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < kept) -> (simplex_mpz_layout )) ”
  &&  “ (kept = 0) ”
  &&  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (UndefStructPredtable ( &( "t" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
.

Definition build_one_sided_partial_solve_wit_9 := build_one_sided_partial_solve_wit_9_pure -> build_one_sided_partial_solve_wit_9_aux.

Definition build_one_sided_partial_solve_wit_10_pure :=
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <> 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (0 < kept)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (N_stable_one_sided_build_normal = N_stable_one_sided_build_normal) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
) \/
(
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept <> 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (0 < kept)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
).

Definition build_one_sided_partial_solve_wit_10_pure_split_goal_1 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept <> 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (0 < kept)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
.

Definition build_one_sided_partial_solve_wit_10_pure_split_goal_2 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <= UINT_MAX)) (PreH2 : (M_stable_one_sided_build_normal <= UINT_MAX)) (PreH3 : (N_stable_one_sided_build_normal <= UINT_MAX)) (PreH4 : (kept >= 0)) (PreH5 : (M_stable_one_sided_build_normal >= 0)) (PreH6 : (N_stable_one_sided_build_normal >= 0)) (PreH7 : (kept <> 0)) (PreH8 : (N_stable_one_sided_build_normal = variables_pre)) (PreH9 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH10 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH11 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH12 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH13 : (0 <= N_stable_one_sided_build_normal)) (PreH14 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH15 : (sizeof(UCHAR) = 1)) (PreH16 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH17 : (0 <= kept)) (PreH18 : (kept <= M_stable_one_sided_build_normal)) (PreH19 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH20 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH21 : (0 < kept)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  ((( &( "head" ) )) # Ptr  |-> head_pre)
  **  ((( &( "variables" ) )) # UInt  |-> N_stable_one_sided_build_normal)
  **  ((( &( "rows" ) )) # UInt  |-> M_stable_one_sided_build_normal)
  **  ((( &( "kept" ) )) # UInt  |-> kept)
  **  ((( &( "signs" ) )) # Ptr  |-> signs)
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  ((( &( "nodes" ) )) # Ptr  |-> nodes)
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
.

Definition build_one_sided_partial_solve_wit_10_aux :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (PreH1 : (kept <> 0)) (PreH2 : (N_stable_one_sided_build_normal = variables_pre)) (PreH3 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH4 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH5 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH6 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH7 : (0 <= N_stable_one_sided_build_normal)) (PreH8 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH9 : (sizeof(UCHAR) = 1)) (PreH10 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH11 : (0 <= kept)) (PreH12 : (kept <= M_stable_one_sided_build_normal)) (PreH13 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH14 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH15 : (0 < kept)),
  (UndefStructPredtable ( &( "t" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) )
|--
  “ (N_stable_one_sided_build_normal = N_stable_one_sided_build_normal) ”
  &&  “ ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) = (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal))))))) -> (simplex_mpz_layout )) ”
  &&  “ (simplex_dimensions_ok (Zlength ((os_shadows (nodes) (0) ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) N_stable_one_sided_build_normal ) ”
  &&  “ (kept <> 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= M_stable_one_sided_build_normal) ”
  &&  “ (simplex_dimensions_ok kept N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < kept) -> (simplex_mpz_layout )) ”
  &&  “ (0 < kept) ”
  &&  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (UndefStructPredtable ( &( "t" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
.

Definition build_one_sided_partial_solve_wit_10 := build_one_sided_partial_solve_wit_10_pure -> build_one_sided_partial_solve_wit_10_aux.

Definition build_one_sided_partial_solve_wit_11 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (retval_cols: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (retval: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals )) (PreH4 : (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ))) (PreH5 : (kept = 0)) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH15 : (0 <= kept)) (PreH16 : (kept <= M_stable_one_sided_build_normal)) (PreH17 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH18 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH19 : (kept = 0)),
  ((&((retval)  # "table" ->ₛ "rows")) # UInt  |-> (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))))
  **  ((&((retval)  # "table" ->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&((retval)  # "table" ->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&((retval)  # "table" ->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&((retval)  # "table" ->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&((retval)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&((retval)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&((retval)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (UndefStructPredtable ( &( "t" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals ) ”
  &&  “ (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal )) ”
  &&  “ (kept = 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= M_stable_one_sided_build_normal) ”
  &&  “ (simplex_dimensions_ok kept N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < kept) -> (simplex_mpz_layout )) ”
  &&  “ (kept = 0) ”
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
  **  ((&((retval)  # "table" ->ₛ "rows")) # UInt  |-> (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))))
  **  (build_input_segment 0 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
.

Definition build_one_sided_partial_solve_wit_12 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (variables_pre: Z) (Masks: (@list Z)) (kept: Z) (signs: Z) (nodes: Z) (nbPtr: Z) (rowPtr: Z) (bPtr: Z) (aPtr: Z) (cPtr: Z) (dPtr: Z) (retval_cols: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (retval: Z) (PreH1 : forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals) (0)) = j))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals )) (PreH4 : (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ))) (PreH5 : (kept <> 0)) (PreH6 : (N_stable_one_sided_build_normal = variables_pre)) (PreH7 : (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal)))) (PreH8 : (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal )) (PreH9 : ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout ))) (PreH10 : ((0 < M_stable_one_sided_build_normal) -> (os_node_layout ))) (PreH11 : (0 <= N_stable_one_sided_build_normal)) (PreH12 : (N_stable_one_sided_build_normal <= INT_MAX)) (PreH13 : (sizeof(UCHAR) = 1)) (PreH14 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))) (PreH15 : (0 <= kept)) (PreH16 : (kept <= M_stable_one_sided_build_normal)) (PreH17 : (simplex_dimensions_ok kept N_stable_one_sided_build_normal )) (PreH18 : ((0 < kept) -> (simplex_mpz_layout ))) (PreH19 : (0 < kept)),
  ((&((retval)  # "table" ->ₛ "rows")) # UInt  |-> (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))))
  **  ((&((retval)  # "table" ->ₛ "cols")) # UInt  |-> retval_cols)
  **  ((&((retval)  # "table" ->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&((retval)  # "table" ->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&((retval)  # "table" ->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&((retval)  # "table" ->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&((retval)  # "table" ->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&((retval)  # "table" ->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (UndefStructPredtable ( &( "t" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
|--
  “ forall (j: Z), (((0 <= j) /\ (j < N_stable_one_sided_build_normal)) -> ((Znth (j) (nbVals) (0)) = j)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) (build_matrix ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals cVals aVals bVals ) ”
  &&  “ (retval_cols = ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal )) ”
  &&  “ (kept <> 0) ”
  &&  “ (N_stable_one_sided_build_normal = variables_pre) ”
  &&  “ (M_stable_one_sided_build_normal = (Zlength (Rows_stable_one_sided_build_normal))) ”
  &&  “ (simplex_dimensions_ok M_stable_one_sided_build_normal N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (simplex_mpz_layout )) ”
  &&  “ ((0 < M_stable_one_sided_build_normal) -> (os_node_layout )) ”
  &&  “ (0 <= N_stable_one_sided_build_normal) ”
  &&  “ (N_stable_one_sided_build_normal <= INT_MAX) ”
  &&  “ (sizeof(UCHAR) = 1) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  “ (0 <= kept) ”
  &&  “ (kept <= M_stable_one_sided_build_normal) ”
  &&  “ (simplex_dimensions_ok kept N_stable_one_sided_build_normal ) ”
  &&  “ ((0 < kept) -> (simplex_mpz_layout )) ”
  &&  “ (0 < kept) ”
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
  **  ((&((retval)  # "table" ->ₛ "rows")) # UInt  |-> (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))))
  **  (build_input_segment nodes 0 (N_stable_one_sided_build_normal + 1 ) (os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))) )
  **  (simplex_malloc_token dPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) dVals )
  **  (simplex_malloc_token cPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) cVals )
  **  (simplex_malloc_token aPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) * sizeof(UINT) ) )
  **  (UIntArray.full bPtr (Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) bVals )
  **  (simplex_malloc_token rowPtr (((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr ((Zlength ((os_shadows (nodes) (0) ((os_kept (variables_pre) (Rows_stable_one_sided_build_normal)))))) + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.full signs N_stable_one_sided_build_normal Masks )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (os_unborrowed_kept N_stable_one_sided_build_normal head_pre Rows_stable_one_sided_build_normal )
  **  (UCharArray.undef_seg nodes (kept * sizeof( "InequList" ) ) (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
.

Definition build_one_sided_partial_solve_wit_13 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (M_stable_one_sided_build_normal: Z) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (kept: Z) (t_addr_rows: Z) (t_addr_cols: Z) (nodes: Z) (signs: Z) (PreH1 : forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals )) (PreH4 : (t_addr_rows = kept)) (PreH5 : (t_addr_cols = (kept + N_stable_one_sided_build_normal ))) (PreH6 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (t_addr_rows = kept) ”
  &&  “ (t_addr_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  (simplex_malloc_token nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  (UCharArray.undef_full nodes (M_stable_one_sided_build_normal * sizeof( "InequList" ) ) )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
.

Definition build_one_sided_partial_solve_wit_14 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (kept: Z) (t_addr_rows: Z) (t_addr_cols: Z) (signs: Z) (PreH1 : forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals )) (PreH4 : (t_addr_rows = kept)) (PreH5 : (t_addr_cols = (kept + N_stable_one_sided_build_normal ))) (PreH6 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))),
  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
  **  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (t_addr_rows = kept) ”
  &&  “ (t_addr_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  (simplex_malloc_token signs N_stable_one_sided_build_normal )
  **  (UCharArray.undef_full signs N_stable_one_sided_build_normal )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
.

Definition build_one_sided_partial_solve_wit_15 :=
forall (Rows_stable_one_sided_build_normal: (@list build_row_snapshot)) (N_stable_one_sided_build_normal: Z) (head_pre: Z) (dPtr: Z) (cPtr: Z) (aPtr: Z) (bPtr: Z) (rowPtr: Z) (nbPtr: Z) (dVals: (@list Z)) (cVals: (@list Z)) (aVals: (@list Z)) (bVals: (@list Z)) (rowVals: (@list Z)) (nbVals: (@list Z)) (kept: Z) (t_addr_rows: Z) (t_addr_cols: Z) (record_return: Z) (PreH1 : forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k))) (PreH2 : (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals )) (PreH3 : (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals )) (PreH4 : (t_addr_rows = kept)) (PreH5 : (t_addr_cols = (kept + N_stable_one_sided_build_normal ))) (PreH6 : (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))))),
  (UndefStructPredtable record_return )
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
|--
  “ forall (k: Z), (((0 <= k) /\ (k < N_stable_one_sided_build_normal)) -> ((Znth (k) (nbVals) (0)) = k)) ”
  &&  “ (simplex_initial_table N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals rowVals ) ”
  &&  “ (simplex_initial_equations N_stable_one_sided_build_normal kept (kept + N_stable_one_sided_build_normal ) (build_matrix ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal)))) dVals cVals aVals bVals ) ”
  &&  “ (t_addr_rows = kept) ”
  &&  “ (t_addr_cols = (kept + N_stable_one_sided_build_normal )) ”
  &&  “ (kept = (Zlength ((os_kept (N_stable_one_sided_build_normal) (Rows_stable_one_sided_build_normal))))) ”
  &&  ((&((record_return)  # "table" ->ₛ "nonbasic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "nonbasic")) # Ptr  |-> nbPtr)
  **  ((&((record_return)  # "table" ->ₛ "row")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "row")) # Ptr  |-> rowPtr)
  **  ((&((record_return)  # "table" ->ₛ "basic")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "basic")) # Ptr  |-> bPtr)
  **  ((&((record_return)  # "table" ->ₛ "a")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "a")) # Ptr  |-> aPtr)
  **  ((&((record_return)  # "table" ->ₛ "c")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "c")) # Ptr  |-> cPtr)
  **  ((&((record_return)  # "table" ->ₛ "d")) # Ptr  |->_)
  **  ((&(( &( "t" ) )->ₛ "d")) # Ptr  |-> dPtr)
  **  ((&((record_return)  # "table" ->ₛ "cols")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "cols")) # UInt  |-> t_addr_cols)
  **  ((&((record_return)  # "table" ->ₛ "rows")) # UInt  |->_)
  **  ((&(( &( "t" ) )->ₛ "rows")) # UInt  |-> t_addr_rows)
  **  (simplex_malloc_token dPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full dPtr kept dVals )
  **  (simplex_malloc_token cPtr (kept * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full cPtr kept cVals )
  **  (simplex_malloc_token aPtr ((kept * (kept + N_stable_one_sided_build_normal ) ) * sizeof( "__mpz_struct" ) ) )
  **  (MpzArray.full aPtr (kept * (kept + N_stable_one_sided_build_normal ) ) aVals )
  **  (simplex_malloc_token bPtr (kept * sizeof(UINT) ) )
  **  (UIntArray.full bPtr kept bVals )
  **  (simplex_malloc_token rowPtr ((kept + N_stable_one_sided_build_normal ) * sizeof(UINT) ) )
  **  (UIntArray.full rowPtr (kept + N_stable_one_sided_build_normal ) rowVals )
  **  (simplex_malloc_token nbPtr (N_stable_one_sided_build_normal * sizeof(UINT) ) )
  **  (UIntArray.full nbPtr N_stable_one_sided_build_normal nbVals )
  **  (build_input_segment head_pre 0 (N_stable_one_sided_build_normal + 1 ) Rows_stable_one_sided_build_normal )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include fme_gmp_Strategy_Correct.
Include safeexec_fme_gmp_Strategy_Correct.

Axiom proof_of_build_one_sided_safety_wit_1 : build_one_sided_safety_wit_1.
Axiom proof_of_build_one_sided_safety_wit_2 : build_one_sided_safety_wit_2.
Axiom proof_of_build_one_sided_safety_wit_3 : build_one_sided_safety_wit_3.
Axiom proof_of_build_one_sided_safety_wit_4 : build_one_sided_safety_wit_4.
Axiom proof_of_build_one_sided_safety_wit_5 : build_one_sided_safety_wit_5.
Axiom proof_of_build_one_sided_safety_wit_6 : build_one_sided_safety_wit_6.
Axiom proof_of_build_one_sided_safety_wit_7 : build_one_sided_safety_wit_7.
Axiom proof_of_build_one_sided_safety_wit_8 : build_one_sided_safety_wit_8.
Axiom proof_of_build_one_sided_safety_wit_9 : build_one_sided_safety_wit_9.
Axiom proof_of_build_one_sided_safety_wit_10 : build_one_sided_safety_wit_10.
Axiom proof_of_build_one_sided_safety_wit_11 : build_one_sided_safety_wit_11.
Axiom proof_of_build_one_sided_safety_wit_12 : build_one_sided_safety_wit_12.
Axiom proof_of_build_one_sided_safety_wit_13 : build_one_sided_safety_wit_13.
Axiom proof_of_build_one_sided_safety_wit_14 : build_one_sided_safety_wit_14.
Axiom proof_of_build_one_sided_safety_wit_15 : build_one_sided_safety_wit_15.
Axiom proof_of_build_one_sided_safety_wit_16 : build_one_sided_safety_wit_16.
Axiom proof_of_build_one_sided_safety_wit_17 : build_one_sided_safety_wit_17.
Axiom proof_of_build_one_sided_safety_wit_18 : build_one_sided_safety_wit_18.
Axiom proof_of_build_one_sided_safety_wit_19 : build_one_sided_safety_wit_19.
Axiom proof_of_build_one_sided_safety_wit_20 : build_one_sided_safety_wit_20.
Axiom proof_of_build_one_sided_safety_wit_21 : build_one_sided_safety_wit_21.
Axiom proof_of_build_one_sided_safety_wit_22 : build_one_sided_safety_wit_22.
Axiom proof_of_build_one_sided_safety_wit_23 : build_one_sided_safety_wit_23.
Axiom proof_of_build_one_sided_safety_wit_24 : build_one_sided_safety_wit_24.
Axiom proof_of_build_one_sided_safety_wit_25 : build_one_sided_safety_wit_25.
Axiom proof_of_build_one_sided_safety_wit_26 : build_one_sided_safety_wit_26.
Axiom proof_of_build_one_sided_safety_wit_27 : build_one_sided_safety_wit_27.
Axiom proof_of_build_one_sided_safety_wit_28 : build_one_sided_safety_wit_28.
Axiom proof_of_build_one_sided_safety_wit_29 : build_one_sided_safety_wit_29.
Axiom proof_of_build_one_sided_safety_wit_30 : build_one_sided_safety_wit_30.
Axiom proof_of_build_one_sided_entail_wit_1 : build_one_sided_entail_wit_1.
Axiom proof_of_build_one_sided_entail_wit_2 : build_one_sided_entail_wit_2.
Axiom proof_of_build_one_sided_entail_wit_3 : build_one_sided_entail_wit_3.
Axiom proof_of_build_one_sided_entail_wit_4 : build_one_sided_entail_wit_4.
Axiom proof_of_build_one_sided_entail_wit_5_1 : build_one_sided_entail_wit_5_1.
Axiom proof_of_build_one_sided_entail_wit_5_2 : build_one_sided_entail_wit_5_2.
Axiom proof_of_build_one_sided_entail_wit_5_3 : build_one_sided_entail_wit_5_3.
Axiom proof_of_build_one_sided_entail_wit_6 : build_one_sided_entail_wit_6.
Axiom proof_of_build_one_sided_entail_wit_7 : build_one_sided_entail_wit_7.
Axiom proof_of_build_one_sided_entail_wit_8 : build_one_sided_entail_wit_8.
Axiom proof_of_build_one_sided_entail_wit_9 : build_one_sided_entail_wit_9.
Axiom proof_of_build_one_sided_entail_wit_10 : build_one_sided_entail_wit_10.
Axiom proof_of_build_one_sided_entail_wit_11_1 : build_one_sided_entail_wit_11_1.
Axiom proof_of_build_one_sided_entail_wit_11_2 : build_one_sided_entail_wit_11_2.
Axiom proof_of_build_one_sided_entail_wit_11_3 : build_one_sided_entail_wit_11_3.
Axiom proof_of_build_one_sided_entail_wit_12 : build_one_sided_entail_wit_12.
Axiom proof_of_build_one_sided_entail_wit_13_1 : build_one_sided_entail_wit_13_1.
Axiom proof_of_build_one_sided_entail_wit_13_2 : build_one_sided_entail_wit_13_2.
Axiom proof_of_build_one_sided_entail_wit_13_3 : build_one_sided_entail_wit_13_3.
Axiom proof_of_build_one_sided_entail_wit_13_4 : build_one_sided_entail_wit_13_4.
Axiom proof_of_build_one_sided_entail_wit_14 : build_one_sided_entail_wit_14.
Axiom proof_of_build_one_sided_entail_wit_15_1 : build_one_sided_entail_wit_15_1.
Axiom proof_of_build_one_sided_entail_wit_15_2 : build_one_sided_entail_wit_15_2.
Axiom proof_of_build_one_sided_return_wit_1 : build_one_sided_return_wit_1.
Axiom proof_of_build_one_sided_partial_solve_wit_1_pure : build_one_sided_partial_solve_wit_1_pure.
Axiom proof_of_build_one_sided_partial_solve_wit_1 : build_one_sided_partial_solve_wit_1.
Axiom proof_of_build_one_sided_partial_solve_wit_2 : build_one_sided_partial_solve_wit_2.
Axiom proof_of_build_one_sided_partial_solve_wit_3 : build_one_sided_partial_solve_wit_3.
Axiom proof_of_build_one_sided_partial_solve_wit_4 : build_one_sided_partial_solve_wit_4.
Axiom proof_of_build_one_sided_partial_solve_wit_5 : build_one_sided_partial_solve_wit_5.
Axiom proof_of_build_one_sided_partial_solve_wit_6_pure : build_one_sided_partial_solve_wit_6_pure.
Axiom proof_of_build_one_sided_partial_solve_wit_6 : build_one_sided_partial_solve_wit_6.
Axiom proof_of_build_one_sided_partial_solve_wit_7 : build_one_sided_partial_solve_wit_7.
Axiom proof_of_build_one_sided_partial_solve_wit_8 : build_one_sided_partial_solve_wit_8.
Axiom proof_of_build_one_sided_partial_solve_wit_9_pure : build_one_sided_partial_solve_wit_9_pure.
Axiom proof_of_build_one_sided_partial_solve_wit_9 : build_one_sided_partial_solve_wit_9.
Axiom proof_of_build_one_sided_partial_solve_wit_10_pure : build_one_sided_partial_solve_wit_10_pure.
Axiom proof_of_build_one_sided_partial_solve_wit_10 : build_one_sided_partial_solve_wit_10.
Axiom proof_of_build_one_sided_partial_solve_wit_11 : build_one_sided_partial_solve_wit_11.
Axiom proof_of_build_one_sided_partial_solve_wit_12 : build_one_sided_partial_solve_wit_12.
Axiom proof_of_build_one_sided_partial_solve_wit_13 : build_one_sided_partial_solve_wit_13.
Axiom proof_of_build_one_sided_partial_solve_wit_14 : build_one_sided_partial_solve_wit_14.
Axiom proof_of_build_one_sided_partial_solve_wit_15 : build_one_sided_partial_solve_wit_15.

End VC_Correct.
